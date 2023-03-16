using DataFrames, Distributed, CSV, InteractiveUtils

function shares_head(x, y) 
    x1 = Base.unwrap_unionall(x)
    y1 = Base.unwrap_unionall(y)
    return x1 isa DataType && y1 isa DataType && x1.name == y1.name
end

function my_methodswith(@nospecialize(t::Type), @nospecialize(f::Base.Callable), meths = []; supertypes::Bool=false)
    for d in methods(f)
        function sig_hastype(x)
            let x = Base.rewrap_unionall(x, d.sig)
                (InteractiveUtils.type_close_enough(x, t) || shares_head(x, t) ||
                        (supertypes ? (isa(x, Type) && t <: x && (!isa(x,TypeVar) || x.ub != Any)) :
                         (isa(x,TypeVar) && x.ub != Any && t == x.ub)) &&
                        x != Any)
            end
        end
        oftype = collect(Iterators.filter((tup) -> sig_hastype(tup[2]), enumerate(Base.unwrap_unionall(d.sig).parameters)))
        if !isempty(oftype)
            push!(meths, (type = t, mname = d.name, argindex=first(oftype)[1], nargs=length(Base.unwrap_unionall(d.sig).parameters),mth=d))
        end
    end
    return meths
end

function _methodswith(@nospecialize(t::Type), m::Module, supertypes::Bool, meths = [], seen=Set{Module}())
    if (m in seen) return meths end
    push!(seen, m)
    for nm in names(m, all=true)
        if isdefined(m, nm)
            f = getfield(m, nm)
            if isa(f, Module)
                _methodswith(t, m, supertypes, meths, seen)
            end
            if isa(f, Base.Callable)
                my_methodswith(t, f, meths; supertypes = supertypes)
            end
        end
    end
    return unique(meths)
end
flat(arr::Array) = mapreduce(x -> x, append!, arr,init=[])

function is_in_module(typ, mod, seen = Set{Module}())
    if mod in seen 
        return false 
    end
    push!(seen, mod) 
    if mod == typ.name.module 
        return true 
    end
    if typ.name.module == Core 
        return true
    end
    return is_in_module(typ, Base.parentmodule(mod), seen)
end
function concrete_subtypes(typ, mod=nothing, out=[])
    try 
        for sub in subtypes(typ)
            basetyp = Base.unwrap_unionall(sub)
            if !isabstracttype(basetyp) && (isnothing(mod) || is_in_module(basetyp, mod))
                push!(out, sub)
            else 
                concrete_subtypes(sub, mod, out)
            end
        end
    catch e
        return []
    end
    return out
end

function find_candidates(fortype, mod)
    impls = flat(_methodswith.(concrete_subtypes(fortype, mod), (mod, ), (true, )))
    if !isempty(impls)
        df = DataFrame(impls)
    else 
        df = DataFrame([:type =>[], :mname =>[], :argindex =>[], :nargs =>[], :mth =>[]])
    end
    candidates = groupby(df, [:mname, :argindex, :nargs])

    supers = _methodswith(fortype, mod, true)
    if !isempty(supers)
        onsuper_base = DataFrame(supers)
    else
        onsuper_base = DataFrame([:type =>[], :mname =>[], :argindex =>[], :nargs =>[], :mth =>[]])
    end
    not_in_super = filter(c->nrow(c) > 1, groupby(antijoin(df, onsuper_base; on=[:mname, :argindex, :nargs]), [:mname, :argindex, :nargs]))
    
    getname_sym(typ) = Base.unwrap_unionall(typ).name.name
    b = Set{Any}(getname_sym.(concrete_subtypes(fortype, mod)))
    filtered = filter(c->let a = Set{Any}(unique(getname_sym.(c[!, :type]))); issubset(a,b) && issubset(b,a) end, not_in_super)
    res=insertcols!(DataFrame(filtered), 1, :abstype => fortype)

    #return fortype, filtered, not_in_super, candidates, df
    return res, (type=fortype, strict_interfaces=length(filtered), partial_interfaces=length(not_in_super), specialized=length(filter(c->nrow(c) > 1, candidates)))
end

function types_recursive(mod, types=[], seen=Set{Module}())
    if (mod in seen) return types end
    push!(seen, mod)
    for name in names(mod, all=true)
        if !isdefined(mod, name)
            continue
        end
        x = getfield(mod, name)
        if x isa Type && isabstracttype(x)
            unwrapped = Base.unwrap_unionall(x)
            if !(mod == Base) && unwrapped isa DataType && (unwrapped.name.module == Base || unwrapped.name.module == Core || unwrapped.name.module==Core.Compiler)
                continue 
            end
            if unwrapped isa DataType && unwrapped.name == Type.body.name
                continue
            end
            push!(types, x)
        end
        if x isa Module 
            types_recursive(x, types, seen)
        end
    end
    return types
end
function analyze_module(mod)
    summary_rows = []
    abstract_types = types_recursive(mod)
    df = DataFrame([:mod=>[], :abstype=>[], :type =>[], :mname =>[], :argindex =>[], :nargs =>[], :mth =>[]])
    for type in abstract_types 
        println(type)
        womod_interfaces, summary = find_candidates(type, mod)
        mod_interfaces = DataFrame(womod_interfaces)
        insertcols!(mod_interfaces, 1, :mod => mod)
        append!(df, DataFrame(mod_interfaces))
        push!(summary_rows, summary)
    end
    return df, DataFrame(summary_rows)
end

function run_analysis(dirname, modname) 
    result_df, result_summary = analyze_module(getfield(Main, modname)) # assumes that the module has already been loaded
    Base.Filesystem.mkpath("test/results/$dirname")
    CSV.write("test/results/$dirname/$(modname)_interfaces.csv", result_df)
    CSV.write("test/results/$dirname/$(modname)_summary.csv", result_summary)
end