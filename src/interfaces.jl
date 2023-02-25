params(t::UnionAll) = params(t.body) + 1
params(t::DataType) = 0
unfold(t::UnionAll) = unfold(t.body)
unfold(t::DataType) = t
unfold(t::TypeVar) = t.ub
unfold(t::Union) = t
unfold(r) = r
unvar(t::DataType) = t
unvar(t::UnionAll) = t 
unvar(t::TypeVar) = t.ub
unvar(r) = r
function find_instance_of_super(bodyty::DataType, ttyname::Core.TypeName)
    if bodyty == Any
        if ttyname != Any.name
            return nothing
        else 
            return bodyty
        end
    end
    if bodyty.name == ttyname 
        return bodyty
    end 
    return find_instance_of_super(supertype(bodyty), ttyname)
end
find_instance_of_super(bodyty::UnionAll, ttyname::Core.TypeName) =
    if unfold(bodyty).name == ttyname 
        bodyty
    else
        find_instance_of_super(supertype(bodyty), ttyname)
    end

isinstance(a,ttyname) = a <: ttyname.wrapper || (a isa DataType && a.name.wrapper <: ttyname.wrapper)

function specialize_matrix(pats::Vector{<:Vector{<:Any}}, ttyname)
    out = Vector{Any}[]
    for pat in pats 
        fp = unfold(first(pat))
        rest = pat[2:end]
        arity = params(ttyname.wrapper)
        println("pat: $fp against: $ttyname isinstance: $(isinstance(fp, ttyname))")
        if fp == Any
            push!(out, [repeat([Any], arity); rest])
        elseif fp isa UnionAll && isinstance(fp, ttyname)
            push!(out, rest)
            body = unfold(fp)
            println("dt")
            if body.name == ttyname
                #push!(out, [collect(unvar.(body.parameters)); rest])
            else 
                #push!(out, [collect(unvar.(unfold(find_instance_of_super(fp, ttyname)).parameters)); rest])
            end
        elseif fp isa DataType && isinstance(fp, ttyname)
            push!(out, rest)
            #push!(out, [unvar.(collect(fp.parameters)); rest])
        elseif fp isa Union
            append!(out, specialize_matrix([[fp.a; rest], [fp.b; rest]], ttyname))
        end
    end
    println("specialized matrix $out for $pats under $ttyname")
    return out
end
function specialize_types(match::Vector{<:Any}, ttyname::Core.TypeName)
    fp = first(match)
    rest = match[2:end]
    #println(supertype(ttyname.wrapper))
    #println(unfold(find_instance_of_super(ttyname.wrapper, unfold(fp).name)).parameters)
    out = [rest]#[unvar.(unfold(fp).parameters); rest]
    println("specialized types $out for $match under $ttyname")
    return out
end

complete_signature(pats::Vector{Core.TypeName}, ty::DataType) = complete_signature(pats, ty.name)
complete_signature(pats::Vector{Core.TypeName}, ty::Union) = complete_signature(pats, ty.a) && complete_signature(pats, ty.b)

function cstr_namesof(ref::Core.TypeName)
    subs = subtypes(ref.wrapper)
    subs = filter(s -> unfold(s).name.module != Core.Compiler, subs)
    return [unfold(sub).name for sub in subs]
end

function complete_signature(pats::Vector{Core.TypeName}, ref::Core.TypeName)
    if ref in pats
        return true
    end
    names = cstr_namesof(ref)
    if length(names) == 0 
        return false
    end
    return all(complete_signature(pats, name) for name in names)
end

function default_matrix(pats::Vector{<:Vector{<:Any}})
    out = Vector{Any}[]
    for row in pats 
        fr = first(row)
        rest = row[2:end]
        if fr == Any 
            push!(out, rest)
        elseif fr isa Union 
            append!(out, default_matrix([[fr.a; rest], [fr.b; rest]]))
        end
    end
    return out
end

getname(t::Type{T}, ref) where T = [unfold(t).name]
getname(t::DataType, ref) = [t.name]
getname(t::Union, ref) = [getname(t.a, ref); getname(t.b, ref)]
getname(r, ref) = []

arity(t::Core.TypeName) = 0 # length(unfold(t.wrapper).parameters)

makepats(mn) = map(m->collect(unfold(m.sig).parameters[2:end]), methods(mn))
makematch(len) = repeat([Any], len)

struct Cstr 
    head::Core.TypeName
    params::Vector{Any}
end
function Base.show(io::IO, c::Cstr) 
    print(io, c.head)
    print(io, "{")
    if length(c.params) > 0
        print(io, c.params)
    end
    print(io, "}")
end
struct Wild end

function filter_pats(pats::Vector{X}, ts::Vector{<:Any}) where X<:Vector{<:Any}
    out = X[]
    for pat in pats 
        if isempty(pat) || (all(map((t, p) -> !(t isa Core.TypeofVararg || p isa Core.TypeofVararg) && (unvar(p) <: t || t <: unvar(p)), ts, pat)) && length(pat) == length(ts))
            push!(out, pat)
        end
    end
    return out
end
function inexhaustive(pats::Vector{<:Vector{<:Any}}, ts::Vector{<:Any}, len)
    pats = filter_pats(pats, ts)
    println("after filtering $pats against $ts with $len")
    if len != length(ts)
        if any(t -> t isa Core.TypeofVararg, ts) return false end
    end
    if len == 0
        if length(pats) == 0
            return []
        else 
            return nothing 
        end
    end
    if first(ts) isa Core.TypeofVararg
        return nothing 
    end
    fstty = unfold(first(ts))
    fsttyname = fstty.name
    firstnames = convert(Vector{Core.TypeName}, vcat(getname.(unfold.(first.(pats)), (fstty, ))...))
    if complete_signature(firstnames, fstty)
        for fn in firstnames
            if isnothing(find_instance_of_super(fn.wrapper, fsttyname)) continue end
            nairty = arity(fn)
            res = inexhaustive(specialize_matrix(pats, fn), specialize_types(ts, fn), nairty + len - 1) 
            if !isnothing(res)
                return [Cstr(fn, res[1:nairty]); res[nairty+1:end]]
            end
        end
        return nothing
    else 
        res = inexhaustive(default_matrix(pats), ts[2:end], len-1)
        if isnothing(res)
            return nothing 
        end
        uncovered = filter(n->!(n in firstnames), cstr_namesof(fstty.name))
        if isempty(uncovered)
            return [Wild(); res]
        else
            sig = first(uncovered)
            return [Cstr(sig, repeat([Wild()], arity(sig))); res]
        end
    end
end