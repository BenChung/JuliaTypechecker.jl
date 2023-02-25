@data JlType begin 
	BasicType(type::Any)
	ModuleType(mod::Module)
	SpecialFunction(fn::Function)
end
Base.show(io::IO, t::BasicType) = "BasicType($(show(io, t.type)))"

canonize(t::JlType) = @match t begin
	BasicType(it) => it
	ModuleType(_) => Module
	SpecialFunction(fn) => typeof(fn)
end

spec_typeof(obj::Core.IntrinsicFunction) = SpecialFunction(obj)
spec_typeof(obj::Type) = BasicType(Type{obj})
spec_typeof(obj::Module) = ModuleType(obj)
spec_typeof(obj) = BasicType(typeof(obj))


isstatictype(b::BasicType, ::Type{V}) where V = b.type <: V
isstatictype(b::BasicType, ::Type{TypeVar}) = b.type isa TypeVar
isstatictype(s::JlType, ::Type{T}) where T = canonize(s) <: T
isstatictype(::Any, ::Any) = false

typemeet(t1::JlType, ts::Vararg{JlType}) = typemeet(JlType[t1, ts...])
typemeet(tys::Vector{T}) where T <: JlType = BasicType(Base.typejoin(canonize.(tys)...))

static_eltype(ty::BasicType) = BasicType(eltype(ty.type))


mutable struct LocalContext
	octx::TypecheckContext
	variables::Base.ImmutableDict{Symbol, JlType}
	return_type::Union{Nothing, JlType}
end

bind(ctx::LocalContext, key::Symbol, value::Definition) = ctx.variables = Base.ImmutableDict(ctx.variables, key=>value)

expand_name_to_path(t::Core.TypeName) = [fullname(t.module)..., t.name]

function lookup_global_type(sym::Symbol) 
	rttype = spec_typeof(lookup_type(sym))
	return rttype # TODO
end
lookup_variable_type(ctx::LocalContext, sym::Symbol) = haskey(ctx.variables, sym) ? ctx.variables[sym] : lookup_global_type(sym)


lookup_type(sym::Symbol) = getproperty(Base, sym)
convert_type(ctx::LocalContext, src, vars::Base.ImmutableDict{Symbol, TypeVar}) = BasicType(convert_type_internal(ctx, src, vars))
convert_type_internal(ctx::LocalContext, src::TypeVarDef, vars::Base.ImmutableDict{Symbol, TypeVar}) = TypeVar(src.var, convert_type_internal(ctx, src.lb, vars), convert_type_internal(ctx, src.ub, vars))

function convert_type_internal(ctx::LocalContext, type::Expression, vars::Base.ImmutableDict{Symbol, TypeVar})
	return @match type begin 
		Variable(:Any, _) => Any
		Variable(sym, _) => sym in keys(vars) ? vars[sym] : lookup_type(sym)
		CallCurly(:Tuple, es, _) => Tuple{convert_type_internal.((ctx, ), es, (vars, ))...}
		CallCurly(:Union, es, _) => Union{convert_type_internal.((ctx, ), es, (vars, ))...}
		CallCurly(rec, es, _) => convert_type_internal(ctx, rec, vars){convert_type_internal.((ctx, ), es, (vars, ))...}
		WhereType(e, tvs, _) => 
			if length(tvs) > 0 
				var = first(tvs)
				converted = TypeVar(var.name, isnothing(var.lb) ? Union{} : convert_type_internal(ctx, var.lb, vars), isnothing(var.ub) ? Any : convert_type_internal(ctx, var.ub, vars))
				UnionAll(converted, convert_type_internal(ctx, e, Base.ImmutableDict(vars, var.name => converted)))
			else
				convert_type_internal(ctx, e, vars) 
			end
	end
end

destruct_tuple_type(t::BasicType) = t.type.name == Tuple.name ? t.parameters : throw("Cannot destruct non-tuple")
destruct_named_tuple_type(t::BasicType) = t.type.name == NamedTuple.name ? t.parameters : throw("Cannot destruct non-tuple")
function extract_tuple_bindings(params::Vector{LValue}, types)
	assignment = []
	ptr = 1
	while ptr <= length(params) && ptr <= length(types)
		param = params[ptr]
		@match param begin 
			VarargAssignment(tgt, _) => begin 
				append!(assignment, extract_bindings(tgt, Tuple{types[i:end]...}))
				break
			end
			_ => append!(assignment, extract_bindings(param, types[ptr]))
		end
		ptr += 1
	end
	return assignment
end

assignable(from::BasicType, to::BasicType) = from.type <: to.type

# a named tuple assignment extracts the values at the names (effectively like getproperty) in one go
# (;x,y) = foo is like going x = foo.x; y = foo.y
function extract_named_tuple_bindings(ctx::LocalContext, params::Vector{Union{IdentifierAssignment, TypedAssignment}}, type)
	param_names = []
	for param in params
		@match param begin 
			IdentifierAssignment(id::Symbol, _) => push!(param_names, id => nothing)
			TypedAssignment(IdentifierAssignment(id::Symbol, _), typ, _) => push!(param_names, id => typ)
		end
	end
	existing_names = fieldnames(canonize(type))
	for (id, decltyp) in param_names
		if !(id in existing_names) 
			throw("$id does not exist in type $type")
		end
		reftype = fieldtype(id, type)
		if !(assignable(reftype, decltype))
			throw("Cannot assign from a property of type $reftype on $type.$id to one of type $decltype")
		end
	end
	return param_names

end

extract_bindings(ctx::LocalContext, binding::LValue, type::JlType) = @match binding begin 
	IdentifierAssignment(id::Symbol, _) => lookup_variable_type(id)
	OuterIdentifierAssignment(id::Symbol, _) => lookup_variable_type(id)
	FieldAssignment(obj::Expression, name::Symbol, _) => 
	TupleAssignment(params::Vector{LValue}, _) => extract_tuple_bindings(params, destruct_tuple_type(type))
	NamedTupleAssignment(params::Vector{Union{IdentifierAssignment, TypedAssignment}}, _) => extract_named_tuple_bindings(ctx, params, type)

	RefAssignment(arr::Expression, arguments::Vector{PositionalArgs}, kwargs::Vector{KeywordArg}, _) => []
	VarargAssignment(tgt, _) => throw("Assigning to varargs outside of tuple context")
	TypedAssignment(lhs::LValue, decltype::Expression, _) => !assignable(type, decltype) ? throw("Invalid assignment from $type to $decltype") : extract_bindings(ctx, lhs, type) # Todo: check safety
	FunctionAssignment(name::FunctionName, args_stmts::Vector{FnArg}, kwargs_stmts::Vector{KwArg}, sparams::Vector{TyVar}, rett::Union{Expression, Nothing}, _) => 
		throw("inline functions not supported yet")
	BroadcastAssignment(lhs::LValue, _) => []
    UnionAllAssignment(name::LValue, tyargs::Vector{TyVar}, _) => throw("Const type aliasing not supported yet")
end

typecheck_lvalue(ctx::LocalContext, binding::LValue) = @match binding begin 
	IdentifierAssignment(id::Symbol, _) => [id => type]
	OuterIdentifierAssignment(id::Symbol, _) => [id => type]
	FieldAssignment(obj::Expression, name::Symbol, _) => begin
		ictx, recty = typecheck_expression(lctx, obj)
		@match recty begin 
			BasicType(typ) => return typecheck_getproperty(ictx, typ, prop)
			ModuleType(md) => return typecheck_module_access(ictx, md, prop)
		end
		throw("not implemented $recty")
	end
	TupleAssignment(params::Vector{LValue}, _) => BasicType(Tuple{canonize.(typecheck_lvalue.((ctx, ), params))...})
	NamedTupleAssignment(params::Vector{Union{IdentifierAssignment, TypedAssignment}}, _) => extract_named_tuple_bindings(ctx, params, type)

	RefAssignment(arr::Expression, arguments::Vector{PositionalArgs}, kwargs::Vector{KeywordArg}, _) => []
	VarargAssignment(tgt, _) => throw("Assigning to varargs outside of tuple context")
	TypedAssignment(lhs::LValue, decltype::Expression, _) => !assignable(type, decltype) ? throw("Invalid assignment from $type to $decltype") : extract_bindings(ctx, lhs, type) # Todo: check safety
	FunctionAssignment(name::FunctionName, args_stmts::Vector{FnArg}, kwargs_stmts::Vector{KwArg}, sparams::Vector{TyVar}, rett::Union{Expression, Nothing}, _) => 
		throw("inline functions not supported yet")
	BroadcastAssignment(lhs::LValue, _) => []
    UnionAllAssignment(name::LValue, tyargs::Vector{TyVar}, _) => throw("Const type aliasing not supported yet")
end

function typecheck_function(ctx::TypecheckContext, 
	name::FunctionName, 
	arguments::Vector{FnArg}, 
	kw_args::Vector{KwArg}, 
	sparams::Vector{TyVar}, 
	rett::Union{Expression, Nothing}, 
	body::Union{Expression, Nothing})
	
	lctx = LocalContext(ctx, Base.ImmutableDict{Symbol, JlType}(), nothing)
	typeargs = Base.ImmutableDict{Symbol, TypeVar}()
	optargs = []
	for tyarg in sparams 
		typeargs = Base.ImmutableDict{Symbol, TypeVar}(typeargs, convert_type(lctx, tyarg, typeargs))
	end
	rtty = !isnothing(rett) ? convert_type(lctx, rett, typeargs) : JuliaTypechecker.BasicType(Any)
	lctx.return_type = rtty
	for arg in arguments 
		argtype = isnothing(arg.type) ? JuliaTypechecker.BasicType(Any) : convert_type(lctx, arg.type, typeargs)
		if !isnothing(arg.binding)
			lctx = bind_argument(lctx, arg.binding, argtype)
		end
		push!(optargs, arg.default_value => argtype)
	end
	for kwarg in kw_args 
		kwarg_type = isnothing(kwarg.type) ? Any : convert_type(lctx, kwarg.type, typeargs)
		if kwarg.is_vararg
			kwarg_type = AbstractDict{Symbol, Any}
		end
		lctx = bind_symbol(lctx, kwarg.name, kwarg_type)
		push!(optargs, arg.default_value => kwarg_type)
	end
	for (defval_expr, reqtype) in optargs
		if isnothing(defval_expr) continue end
		lctx, rty = typecheck_expression(lctx, defval_expr)
		if !assignable(rty, reqtype)
			throw("invalid argument of type $rty needed $reqtype")
		end
	end

	if !isnothing(body)
		lctx, rty = typecheck_expression(lctx, body)
		if !assignable(rty, rtty)
			throw("cannot assign from the real return type $rty to the required $rtty")
		end
	end
	return BasicType(Function)
end

function bind_argument(lctx::LocalContext, binding::LValue, value::JlType) 
	extracted = extract_bindings(lctx, binding, value)
	nctx = lctx.variables
	for (name, type) in extracted 
		nctx = Base.ImmutableDict(nctx, name=>type)
	end
	LocalContext(lctx.octx, nctx, lctx.return_type)
end
get_variable(lctx::LocalContext, var::Symbol) = lctx.variables[var]

function dispatch_typed_direct(fn::Union{Function,DataType}, canonical_args)
    #println(args)
    world = ccall(:jl_get_tls_world_age, UInt, ())
    interp = Core.Compiler.NativeInterpreter(world)
    if fn isa Core.IntrinsicFunction
        throw(IntrinsicPassedException(fn))
    elseif fn <: Core.Builtin # we can be assured it exists?
        rt = Core.Compiler.builtin_tfunction(interp, fn.instance, Any[canonical_args...], nothing)
        #println("invoking builtin $fn with arguments $(canonical_args...) to return $rt")
        if isa(rt, TypeVar)
            return rt.ub
        else
            return Core.Compiler.widenconst(rt)
        end
    end
    if fn <: Function
        fn_rec = fn
    else
        fn_rec = fn # fn.parameters[1]
    end
    argtuple = Tuple{fn,canonical_args...}
    #@debug ("Fetching method $fn_rec with signature $(canonical_args) with fn $fn fnty $(typeof(fn))")
    directly_callable = Base._methods_by_ftype(Tuple{fn_rec,canonical_args...}, -1, typemax(UInt64))
    if length(directly_callable) > 0 # there is a method that we can
        has_candidate = false
        rt = Union{}
        for mdef in directly_callable
            println("calling method on $mdef")
            println("is $argtuple <: $(mdef.method.sig)? $(argtuple <: mdef.method.sig) and args $(argtuple)")
            rty = Core.Compiler.typeinf_type(interp, mdef.method, mdef.spec_types, mdef.sparams)
            rt = Core.Compiler.tmerge(rty, rt)
            println("Callable $((mdef::Core.MethodMatch).method.sig), returning $rty, acc rty $rt")
			has_candidate = true
        end
        if has_candidate
            return BasicType(rt)
        end
        # todo: check if there's an interface declared for this type
    end
	buff = IOBuffer()
	dump(buff, fn_rec)
	@debug "accessing instance on $(read(buff, String)) $(fn_rec === nothing)"
    instance = fn_rec.instance
    output = """Invalid method call $fn_rec with args $canonical_args
    	Searching for functions using signature $argtuple within $directly_callable; attempts:
    	$(join(["$(mdef.method.sig); argtuple <: typ?: $(argtuple <: mdef.method.sig)" for mdef in directly_callable], "\n"))
    	out of all methods
    	$(methods(instance))
    """
    @debug "throwing error $output"
    throw(output)
end

function typecheck_fn_call(lctx::LocalContext, receiver::Expression, pos_args::Vector{PositionalArgs}, kw_args::Vector{Union{KeywordArg, SplatArg}})
	fnty = typecheck_expression(lctx, receiver)

	ictx = lctx
	(ictx, rectyp) = typecheck_expression(ictx, receiver)
	argtyps = []
	for arg in pos_args
		@match arg begin
			PositionalArg(body, _) => begin
				(ictx, argty) = typecheck_expression(ictx, body)
				push!(argtyps, argty)
			end
			SplatArg(body, _) => begin 
				ictx, argty = typecheck_expression(ictx, body)
				splatted = []
				if argty.name == Tuple.name || argty.name == NamedTuple.name
					splatted = collect(fieldtypes(argty))
				elseif assignable(argty, AbstractArray)
					throw("Variable-length splatting is not currently supported!")
				else 
					throw("Splatting of $argty is not allowed!")
				end
				append!(argtyps, splatted)
			end
		end
	end
	kwtyps = []
	for arg in kw_args
		@match arg begin
			KeywordArg(name, body, _) => begin
				(ictx, argty) = typecheck_expression(ictx, body)
				push!(kwtyps, name=>argty)
			end
			SplatArg(body, _) => begin 
				ictx, argty = typecheck_expression(ictx, body)
				splatted = []
				if argty.name == NamedTuple.name
					splatted = (=>).(fieldnames(argty), fieldtypes(argty))
				elseif assignable(argty, AbstractArray)
					throw("Variable-length splatting is not currently supported!")
				else 
					throw("Splatting of $argty is not allowed!")
				end
				append!(kwtyps, splatted)
			end
		end
	end

	if length(kw_args) > 0
		func = Core.kwfunc(rectyp)
		if length(methods(func)) == 0
			throw("$func is not a keywords function type")
		end
		ntty = NamedTuple{(first.(kwtyps)...), Tuple{last.(kwtyps)...}}
		res = dispatch_typed_direct(canonize(func), canonize.([ntty; rectyp; argtyps]))
		return (ictx, res)
	else 
		res = dispatch_typed_direct(canonize(rectyp), canonize.(argtyps))
		return (ictx, res)
	end
end

#no I'm not proud
getproperty_helper(x::T, name::Val{Sym}) where {T, Sym} = getproperty(x, Sym)
typecheck_getproperty(ictx::LocalContext, typ, prop::Union{Symbol, Literal}) = @match prop begin
	s::Symbol => (ictx, dispatch_typed_direct(typeof(getproperty_helper), [typ, Val{s}]))
	Literal(vl, _) => (ictx, dispatch_typed_direct(typeof(getproperty_helper), [typ, Val{vl}]))
end
typecheck_module_access(ictx::LocalContext, mod, prop::Union{Symbol, Literal}) = @match prop begin 
	s::Symbol => (ictx, get)
end

literal_typeof(e) = BasicType(typeof(e))
function typecheck_expression(lctx::LocalContext, expr::Expression)
	@match expr begin 
		Literal(expr::Any, _) => (lctx, literal_typeof(expr))
		Variable(name::Symbol, _) => (lctx, lookup_variable_type(lctx, name))
		FunctionDef(name::FunctionName, arguments::Vector{FnArg}, kw_args::Vector{KwArg}, sparams::Vector{TyVar}, rett::Union{Expression, Nothing}, body::Union{Expression, Nothing}, _) => 
			(lctx, typecheck_function(lctx.octx, name, arguments, kw_args, sparams, rett, body))
		MacroDef(name::ResolvedName, arguments::Vector{FnArg}, sparams::Vector{TyVar}, rett::Union{Expression, Nothing}, body::Union{Expression, Nothing}, _) => 
			throw("not implemented")
		Block(exprs::Vector{Expression}, _) => begin 
			(lctx, rtty) = (lctx, Nothing)
			for expr in exprs 
				(lctx, rtty) = typecheck_expression(lctx, expr)
			end
			return (lctx, rtty)
		end
		LetBinding(bindings::Vector{Union{Pair{<:LValue, <:Expression}, Symbol}}, body::Expression, _) => begin
			ictx = lctx
			for binding in bindings 
				if !(binding isa Symbol)
					(ictx, bodytype) = typecheck_expression(lctx, binding[2])
					ictx = bind_argument(ictx, binding[1], bodytype)
				end
			end
			_, rtty = typecheck_expression(ictx, body)
		end
		TryCatch(body::Expression, catch_var::Union{Symbol, Nothing}, catch_body::Union{Expression, Nothing}, 
				                   else_body::Union{Expression, Nothing}, finally_body::Union{Expression, Nothing}, _) => throw("not implemented")
		CallCurly(receiver::Expression, args::Vector{Union{Expression, TyVar}}, _) => throw("not implemented")
		Comparison(first::Expression, clauses::Vector{Pair{Expression, Expression}}, _) => throw("not implemented")
		SemanticAST.Broadcast(op::Expression, _) => throw("not implemented")
		FunCall(receiver::Expression, pos_args::Vector{PositionalArgs}, kw_args::Vector{Union{KeywordArg, SplatArg}}, _) => typecheck_fn_call(lctx, receiver, pos_args, kw_args)
		GetIndex(arr::Expression, arguments::Vector{PositionalArgs}, _) => throw("not implemented")
		GetProperty(rec::Expression, prop::Union{Symbol, Literal}, _) => begin
			ictx, recty = typecheck_expression(lctx, rec)
			@match recty begin 
				BasicType(typ) => return typecheck_getproperty(ictx, typ, prop)
				ModuleType(md) => return typecheck_module_access(ictx, md, prop)
			end
			throw("not implemented $recty")
		end
		Assignment(lhs::LValue, rhs::Expression, _) => begin 
			ictx, argty = typecheck_expression(lctx, rhs)
			(bind_argument(ictx, lhs, argty), argty)
		end
		Update(op::Symbol, lhs::LValue, rhs::Expression, dotted::Bool, _) => throw("not implemented")
		WhereType(type::Expression, vars::Vector{TyVar}, _) => throw("not implemented")
		Declaration(vars::Vector{VarDecl}, _) => throw("not implemented")
		DoStatement(func::Expression, arguments::Vector{FnArg}, body::Expression, _) => throw("not implemented")
		TupleExpr(exprs::Vector{Union{Expression, Splat}}, _) => throw("not implemented")
		NamedTupleExpr(exprs::Vector{NamedTupleBody}, _) => throw("not implemented")
		StringInterpolate(components::Vector{Union{String, Expression}}, _) => throw("not implemented")
		TypeAssert(val::Expression, typ::Expression, _) => throw("not implemented")
		IfStmt(clauses::Vector{IfClause}, _) => throw("not implemented")
		WhileStmt(cond::Expression, body::Expression, _) => throw("not implemented")
		BreakStmt(_) => throw("not implemented")
		ContinueStmt(_) => throw("not implemented")
		ReturnStmt(retval::Union{Expression, Nothing}, _) => throw("not implemented")
		ForStmt(iters::Vector{Pair{LValue, Expression}}, body::Expression, _) => throw("not implemented")
		Vect(elems::Vector{Union{Expression, Splat}}, _) => throw("not implemented")
		HCat(type::Union{Expression, Nothing}, elems::Vector{Union{Expression, Splat}}, _) => throw("not implemented")
		VCat(type::Union{Expression, Nothing}, rows::Vector{Union{Row, Expression, Splat}}, _) => throw("not implemented")
		NCat(type::Union{Expression, Nothing}, dim::Int, rows::Vector{Union{NRow, Expression}}, _) => throw("not implemented")
		Generator(flatten::Bool, expr::Expression, iterators::Vector{Iterspec}, _) => throw("not implemented")
		Comprehension(type::Union{Expression, Nothing}, gen::Generator, _) => throw("not implemented")
		Quote(ast::JuliaSyntax.SyntaxNode, _) => throw("not implemented")
		MacroExpansion(value::Any, _) => throw("not implemented")
		Ternary(cond::Expression, then::Expression, els::Expression, _) => throw("not implemented")
	end
end


typecheck(ctx::TypecheckContext, expr::SemanticAST.ToplevelStmts) = @match expr begin
    ToplevelStmt(exprs, _) => foldl((tctx, exp) -> typecheck(ctx, tctx, exp), exprs; init=tctx)
	ExprStmt(FunctionDef(name, arguments, kwargs, sparams, rett, body, _), _) => typecheck_function(ctx, name, arguments, kwargs, sparams, rett, body)
    _ => begin println(expr); return tctx end
end
