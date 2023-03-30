@data JlType begin 
	BasicType(type::Any)
	ModuleType(mod::Module)
	SpecialFunction(fn::Function)
	FunctionType(argtype::JlType, retty::JlType)
end
function Base.show(io::IO, t::BasicType) 
	print(io, "BasicType(")
	show(io, t.type)
	print(io, ")")
end

canonize(t::JlType) = @match t begin
	BasicType(it) => it
	ModuleType(_) => Module
	FunctionType(_, _) => Function
	SpecialFunction(fn) => typeof(fn)
end

ub_tyvar(v::TypeVar) = v.ub
ub_tyvar(t) = t

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

unpack_typeof(t::BasicType) =
	t.type isa Type ? t.type.parameters[1] : throw("Cannot unpack a non-type")

function make_error(ctx::TypecheckContext, element::ASTNode, msg::String, fallback::JlType) 
    ctx.ledger[ctx.node_mapping[element]] = TypeError(msg)
	return fallback
end

static_eltype(ty::BasicType) = BasicType(eltype(ty.type))

mutable struct LocalContext
	octx::TypecheckContext
	variables::Base.ImmutableDict{Symbol, JlType}
	return_type::Union{Nothing, JlType}
	in_array::Union{Nothing, JlType} # stores if we're currently in an indexer expression and are thus allowed to use the end operator
	scope_info::ScopeInfo
	LocalContext(octx::TypecheckContext, variables::Base.ImmutableDict{Symbol, JlType}, return_type::Union{Nothing, JlType}, scope_info::ScopeInfo) = new(octx, variables, return_type, nothing, scope_info)
	LocalContext(bctx::LocalContext) = new(bctx.octx, bctx.variables, bctx.return_type, bctx.in_array, bctx.scope_info)
end



function add_return(ctx::LocalContext, (@nospecialize tgt::ASTNode), rtty::JlType)
	if !assignable(rtty, ctx.return_type)
		make_error(ctx.octx, tgt, "Invalid return type $rtty cannot be assigned to $(ctx.return_type)!");
	end
	return ctx
end

bind(ctx::LocalContext, key::Symbol, value::Definition) = ctx.variables = Base.ImmutableDict(ctx.variables, key=>value)

expand_name_to_path(t::Core.TypeName) = [fullname(t.module)..., t.name]

get_scope_info(ctx::TypecheckContext, node::ASTNode) = find_parent_component(ScopeInfo, ctx, node)

function lookup_type(ctx::LocalContext, sym::Symbol, (@nospecialize loc::ASTNode))
	mod = foldl((mod, modname) -> getfield(mod, modname), ctx.scope_info.path; init=Base)
	if !isdefined(mod, sym)
		make_error(ctx.octx, loc, "Type $sym not found in $mod")
		return Any
	else
		return getproperty(mod, sym)
	end
end

function lookup_global_type(ctx::LocalContext, sym::Symbol, (@nospecialize loc::ASTNode))
	mod = foldl((mod, modname) -> getfield(mod, modname), ctx.scope_info.path; init=Base)
	if !isdefined(mod, sym)
		rttype = make_error(ctx.octx, loc, "Variable $sym not found in $mod", BasicType(Any))
	else
		rttype = spec_typeof(getproperty(mod, sym))
	end
	return rttype # TODO
end
function has_global_variable(sym::Symbol)
	return isdefined(Base, sym)
end
variable_defined(ctx::LocalContext, sym::Symbol) = haskey(ctx.variables, sym) ? true : has_global_variable(sym)
lookup_variable_type(ctx::LocalContext, sym::Symbol, loc::ASTNode) = haskey(ctx.variables, sym) ? ctx.variables[sym] : lookup_global_type(ctx, sym, loc)

convert_type(ctx::LocalContext, src) = convert_type(ctx, src, Base.ImmutableDict{Symbol, TypeVar}())
convert_type(ctx::LocalContext, src, vars::Base.ImmutableDict{Symbol, TypeVar}) = BasicType(convert_type_internal(ctx, src, vars))
convert_type_internal(ctx::LocalContext, src::TyVar, vars::Base.ImmutableDict{Symbol, TypeVar}) = 
	TypeVar(isnothing(src.name) ? gensym("TyVar") : src.name, 
			isnothing(src.lb) ? Union{} : convert_type_internal(ctx, src.lb, vars), 
			isnothing(src.ub) ? Any : convert_type_internal(ctx, src.ub, vars))


evaluate_type_src(ctx::LocalContext, src::Expression) = @match src begin 
	GetProperty(src, name, _) => getproperty(evaluate_type_src(ctx, src), name)
	Variable(sym, _) => lookup_type(ctx, sym, src)
end
function convert_type_internal(ctx::LocalContext, type::Expression, vars::Base.ImmutableDict{Symbol, TypeVar})
	return @match type begin 
		Quote(ast::JuliaSyntax.SyntaxNode, _) => begin 
			if JuliaSyntax.kind(JuliaSyntax.head(ast)) == JuliaSyntax.K"quote" && typeof(JuliaSyntax.Expr(JuliaSyntax.child(ast, 1))) == Symbol 
				JuliaSyntax.Expr(JuliaSyntax.child(ast, 1))
			else 
				make_error(ctx.octx, type, "Static checking does not support quotations in types"); Any 
			end # todo
		end
		Quote(_, _) => begin make_error(ctx.octx, type, "Static checking does not support quotations in types"); Any end
		Variable(:Any, _) => Any
		Variable(sym, _) => begin
			if sym in keys(vars) 
				vars[sym] 
			elseif sym in keys(ctx.variables)
				varty = lookup_variable_type(ctx, sym, type)
				return unpack_typeof(varty)
			else 
				res = lookup_type(ctx, sym, type)
				return res
			end
		end
		CallCurly(:Tuple, es, _) => Tuple{convert_type_internal.((ctx, ), es, (vars, ))...}
		CallCurly(:Union, es, _) => Union{convert_type_internal.((ctx, ), es, (vars, ))...}
		CallCurly(rec, es, _) => begin 
			args = convert_type_internal.((ctx, ), es, (vars, ))
			callee = convert_type_internal(ctx, rec, vars)
			callee{args...}
		end
		WhereType(e, tvs, _) => 
			if length(tvs) > 0 
				newvars = []
				for var in tvs 
					converted = TypeVar(var.name, isnothing(var.lb) ? Union{} : convert_type_internal(ctx, var.lb, vars), isnothing(var.ub) ? Any : convert_type_internal(ctx, var.ub, vars))
					vars = Base.ImmutableDict(vars, var.name => converted)
					push!(newvars, converted)
				end
				res = convert_type_internal(ctx, e, vars)
				for newvar in newvars 
					res = UnionAll(newvar, res)
				end
				return res
			else
				convert_type_internal(ctx, e, vars) 
			end
		FunCall(Variable(:typeof, _), [PositionalArg(arg, _)], _, _) => BasicType(Type{canonize(last(typecheck_expression(ctx, arg)))})
		GetProperty(src, name, _) && prop => evaluate_type_src(ctx, prop)
		other => begin make_error(ctx.octx, type, "Unrecognized form in type $other"); Any end
	end
end

destruct_tuple_type(ctx::LocalContext, loc::ASTNode, t::BasicType) = t.type isa DataType && t.type.name == Tuple.name ? BasicType.(collect(t.type.parameters)) : begin make_error(ctx.octx, loc, "Cannot destruct non-tuple $(t.type)!"); BasicType[] end;
destruct_tuple_type(ctx::LocalContext, loc::ASTNode, t::Nothing) = []
destruct_named_tuple_type(ctx::LocalContext, loc::ASTNode, t::BasicType) = t.type.name == NamedTuple.name ? t.parameters : begin make_error(ctx.octx, loc, "Cannot destruct non-tuple $(t.type)!"); BasicType[] end
destruct_named_tuple_type(ctx::LocalContext, loc::ASTNode, t::Nothing) = []
extract_tuple_bindings(params::Vector{LValue}, ::Nothing) = []
function extract_tuple_bindings(ctx::LocalContext, params::Vector{LValue}, types)
	assignment = []
	ptr = 1
	while ptr <= length(params) && ptr <= length(types)
		param = params[ptr]
		@match param begin 
			VarargAssignment(tgt, _) => begin 
				append!(assignment, typecheck_lvalue(ctx, tgt, Tuple{types[i:end]...}))
				break
			end
			_ => append!(assignment, typecheck_lvalue(ctx, param, types[ptr]))
		end
		ptr += 1
	end
	return assignment
end

function assignable(from::BasicType, to::BasicType) 
	if from.type isa TypeVar && to.type isa TypeVar 
		return from.type.ub <: to.type.ub
	end
	if from.type isa TypeVar 
		return from.type.ub <: to.type
	end
	if to.type isa TypeVar
		return from.type <: to.type.ub
	end
	return from.type <: to.type
end
itertype(over::BasicType) = BasicType(eltype(over.type))

# a named tuple assignment extracts the values at the names (effectively like getproperty) in one go
# (;x,y) = foo is like going x = foo.x; y = foo.y
function extract_named_tuple_bindings(ctx::LocalContext, params::Vector{Union{IdentifierAssignment, TypedAssignment}}, type)
	if isnothing(type) return [] end
	param_names = []
	existing_names = fieldnames(canonize(type)) 
	function check_name(param::IdentifierAssignment, id::Symbol)
		if !(id in existing_names) 
			make_error(ctx.octx, param, "$id does not exist in type $type")
		end
		reftype = fieldtype(id, type)
		if !(assignable(reftype, decltype))
			make_error(ctx.octx, param, "Cannot assign from a property of type $reftype on $type.$id to one of type $decltype")
		end
		return id
	end
	for param in params
		@match param begin 
			IdentifierAssignment(id::Symbol, _) && ida => push!(param_names, check_name(ida, id) => nothing)
			TypedAssignment(IdentifierAssignment(id::Symbol, _) && ida, typ, _) => push!(param_names, check_name(ida, id) => typ)
		end
	end
	return param_names
end
extract_named_tuple_bindings(ctx::LocalContext, params::Vector{Union{IdentifierAssignment, TypedAssignment}}, ::Nothing) = []

function typecheck_assignment(ctx::LocalContext, (@nospecialize obj::Expression), name::Symbol)
	ictx, recty = typecheck_expression(ctx, obj)
	@match recty begin 
		BasicType(typ) => return typecheck_getproperty(ictx, typ, prop)
		ModuleType(md) => return typecheck_module_access(ictx, md, prop)
	end
	throw("not implemented $recty")
end

function typecheck_tuple_lvalue(ctx::LocalContext, params::Vector{<:LValue}, tparams::Vector{<:JlType})
	ictx = ctx
	rtys = JlType[]
	assignment = []
	ptr = 1
	while ptr <= length(params) && ptr <= length(tparams)
		param = params[ptr]
		@match param begin 
			VarargAssignment(tgt, _) => begin 
				(ictx, rty, bindings) = typecheck_lvalue(ictx, param, tparams[ptr:end])
				push!(rtys, rty)
				append!(assignment, bindings)
				break
			end
			_ => begin 
				(ictx, rty, bindings) = typecheck_lvalue(ictx, param, tparams[ptr])
				push!(rtys, rty)
				append!(assignment, bindings)
			end
		end
		ptr += 1
	end
	return (ictx, rtys, assignment)
end

function typecheck_ref(ctx::LocalContext, (@nospecialize ref::ASTNode), (@nospecialize arr::Expression), pos_args::Vector{PositionalArgs}, kw_args::Vector{KeywordArg}, tty::JlType)
	(ictx, rec) = typecheck_expression(ctx, arr)
	(ictx, argtyps, kwtyps) = typecheck_fn_arguments(ictx, pos_args, kw_args)
	(ictx, res) = typecheck_fn_call(ictx, ref, BasicType(typeof(Base.setindex!)), [rec; tty; argtyps], kwtyps)
	return (ictx, tty)
end
function typecheck_ref(ctx::LocalContext, (@nospecialize ref::ASTNode), (@nospecialize arr::Expression), pos_args::Vector{PositionalArgs}, kw_args::Vector{KeywordArg}, tty::Nothing)
	(ictx, rec) = typecheck_expression(ctx, arr)
	(ictx, argtyps, kwtyps) = typecheck_fn_arguments(ictx, pos_args, kw_args)
	(ictx, res) = typecheck_fn_call(ictx, ref, BasicType(typeof(Base.getindex)), [rec; argtyps], kwtyps)
	return (ictx, res)
end

typecheck_lvalue(ctx::LocalContext, binding::LValue, (@nospecialize type::Union{JlType, Nothing})) = @match binding begin 
	IdentifierAssignment(id::Symbol, _) => (ctx, variable_defined(ctx, id) ? lookup_variable_type(ctx, id, binding) : type, [id=>type])
	OuterIdentifierAssignment(id::Symbol, _) => (ctx, variable_defined(ctx, id) ? lookup_variable_type(ctx, id, binding) : type, [id=>type])
	FieldAssignment(obj::Expression, name::Symbol, _) => (typecheck_assignment(ctx, obj, name)..., [])
	TupleAssignment(params::Vector{LValue}, _) => let tparams = destruct_tuple_type(ctx, binding, type); typecheck_tuple_lvalue(ctx, params, tparams) end
	NamedTupleAssignment(params::Vector{Union{IdentifierAssignment, TypedAssignment}}, _) =>  (typecheck_tuple_lvalue(ctx, params)..., extract_named_tuple_bindings(ctx, params, type))
	RefAssignment(arr::Expression, arguments::Vector{PositionalArgs}, kwargs::Vector{KeywordArg}, _) => (typecheck_ref(ctx, binding, arr, arguments, kwargs, type)..., [])
	VarargAssignment(tgt, _) => begin make_error(ctx.octx, binding, "Assigning to varargs outside of tuple context"); (ctx, BasicType(Nothing), []) end
	TypedAssignment(lhs::LValue, decltype::Expression, _) => 
		if !isnothing(type)
			tgtty = convert_type(ctx, decltype)
			if !assignable(type, tgtty)
				make_error(ctx.octx, binding, "Invalid assignment from $type to $decltype")
			end
			return typecheck_lvalue(ctx, lhs, tgtty)
		else
			(ictx, rty, bnds) = typecheck_lvalue(ctx, lhs, type)
			(ictx, decltype, bnds)
		end
	FunctionAssignment(name::FunctionName, args_stmts::Vector{FnArg}, kwargs_stmts::Vector{KwArg}, sparams::Vector{TyVar}, rett::Union{Expression, Nothing}, _) => 
		throw("inline functions not supported yet")
    UnionAllAssignment(name::LValue, tyargs::Vector{TyVar}, _) => throw("Type aliasing not supported yet")
end

@component struct FunctionInfo
	namestring::String
	nabstract::Int
	nconcrete::Int
end
function typecheck_function(ctx::TypecheckContext, 
	scope_info::ScopeInfo,
	name::FunctionName, 
	arguments::Vector{FnArg}, 
	kw_args::Vector{KwArg}, 
	sparams::Vector{TyVar}, 
	(@nospecialize rett::Union{Expression, Nothing}), 
	(@nospecialize body::Union{Expression, Nothing}))
	nconcrete = 0 
	nabstract = 0

	lctx = LocalContext(ctx, Base.ImmutableDict{Symbol, JlType}(), nothing, scope_info)
	typeargs = Base.ImmutableDict{Symbol, TypeVar}()
	optargs = []
	for tyarg in sparams 
		typeargs = Base.ImmutableDict{Symbol, TypeVar}(typeargs, tyarg.name, convert_type_internal(lctx, tyarg, typeargs))
	end
	rtty = !isnothing(rett) ? convert_type(lctx, rett, typeargs) : JuliaTypechecker.BasicType(Any)
	lctx.return_type = rtty
	for arg in arguments 
		argtype = isnothing(arg.type) ? JuliaTypechecker.BasicType(Any) : convert_type(lctx, arg.type, typeargs)
		if !isnothing(arg.binding)
			lctx = bind_argument(lctx, arg.binding, argtype)
		end
		if isabstracttype(canonize(argtype)) || canonize(argtype) isa TypeVar
			nabstract += 1
		else
			nconcrete += 1
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
			make_error(ctx.octx, defval_expr, "invalid argument of type $rty needed $reqtype")
		end
	end

	nvars = lctx.variables
	for (name, var) in typeargs 
		nvars = Base.ImmutableDict(nvars, name=>BasicType(Type{var}))
	end
	lctx = LocalContext(lctx)
	lctx.variables = nvars
	
    lctx.octx.ledger[lctx.octx.node_mapping[name]] = FunctionInfo(string(name), nabstract, nconcrete)

	if !isnothing(body)
		lctx, rty = typecheck_expression(lctx, body)
		if rty isa Type 
			println(body)
		end
		if !assignable(rty, rtty)
			make_error(ctx, body, "cannot assign from the return type $rty to the required $rtty")
		end
	end
	return BasicType(Function)
end

function bind_argument(lctx::LocalContext, (@nospecialize binding::LValue), value::JlType) 
	(ictx, retty, extracted) = typecheck_lvalue(lctx, binding, value)
	nctx = ictx.variables
	for (name, type) in extracted 
		nctx = Base.ImmutableDict(nctx, name=>type)
	end
	out = LocalContext(ictx)
	out.variables = nctx
	return out
end
get_variable(lctx::LocalContext, var::Symbol) = lctx.variables[var]

dispatch_typed_direct(ctx::LocalContext, (@nospecialize loc::ASTNode), fn::TypeVar, args) = dispatch_typed_direct(ctx, loc, fn.ub, args)
dispatch_typed_direct(ctx::LocalContext, (@nospecialize loc::ASTNode), un::Union, args) = typemeet(dispatch_typed_direct(ctx, loc, un.a, args), dispatch_typed_direct(ctx, loc, un.b, args))


@component struct Dispatch 
	argtypes::Vector{Any}
	returns::Any
end
unpack_vars(ctx::LocalContext, typ, used::Set{TypeVar}, shadowed::Base.ImmutableDict{Symbol, Nothing}) = typ # todo: recurse into unions/datatypes
function unpack_vars(ctx::LocalContext, typ::DataType, used::Set{TypeVar}, shadowed::Base.ImmutableDict{Symbol, Nothing}) 
	if length(typ.parameters) == 0 return typ end
	vars = unpack_vars.((ctx, ), typ.parameters, (used, ), (shadowed, ))
	return typ.name.wrapper{vars...}
end
unpack_vars(ctx::LocalContext, typ::UnionAll, used::Set{TypeVar}, shadowed::Base.ImmutableDict{Symbol, Nothing}) = UnionAll(typ.var, unpack_vars(ctx, typ.body, used, Base.ImmutableDict(shadowed, typ.var.name => nothing)))
function unpack_vars(ctx::LocalContext, typ::TypeVar, used::Set{TypeVar}, shadowed::Base.ImmutableDict{Symbol, Nothing})
	if haskey(shadowed, typ.name) || !haskey(ctx.variables, typ.name)
		return typ
	else 
		push!(used, typ)
		return typ
	end
end
function wrap_type(typ, vars::Set{TypeVar})
	for var in vars 
		typ = UnionAll(var, typ)
	end
	return typ
end

function dispatch_typed_direct(ctx::LocalContext, (@nospecialize loc::ASTNode), (@nospecialize fn::Union{Function,DataType, Type{T} where T}), (@nospecialize canonical_args))
    #println("dispatching onto $fn with args $canonical_args")
	rt = Any
    world = ccall(:jl_get_tls_world_age, UInt, ())
    interp = Core.Compiler.NativeInterpreter(world)
    if fn isa Core.IntrinsicFunction
        throw(IntrinsicPassedException(fn))
    elseif fn <: Core.Builtin # we can be assured it exists?
		#println("is builtin")
		if !isdefined(fn, :instance)
			println("Not defined instance $fn")
		end
        rt = Core.Compiler.builtin_tfunction(interp, fn.instance, Any[canonical_args...], nothing)
        #println("invoking builtin $fn with arguments $(canonical_args...) to return $rt")
        if isa(rt, TypeVar)
            return BasicType(rt.ub)
        else
            return BasicType(Core.Compiler.widenconst(rt))
        end
    end
    if fn <: Function
        fn_rec = fn
    else
        fn_rec = fn # fn.parameters[1]
    end
	used = Set{TypeVar}(); shadowed = Base.ImmutableDict{Symbol, Nothing}()
	canonical_args = (unpack_vars.((ctx, ), canonical_args, (used, ), (shadowed, )))
    argtuple = wrap_type(Tuple{fn,canonical_args...}, used)
    directly_callable = Base._methods_by_ftype(Tuple{fn_rec,canonical_args...}, -1, typemax(UInt64))
	output = ""
	try
		#println("callables: $directly_callable")
		if length(directly_callable) > 0 # there is a method that we can
			has_candidate = false
			rt = Union{}
			for mdef in directly_callable
				#println("calling method on $mdef")
				#println("is $argtuple <: $(mdef.method.sig)? $(argtuple <: mdef.method.sig) and args $(argtuple)")
				rty = Core.Compiler.typeinf_type(interp, mdef.method, mdef.spec_types, mdef.sparams)
				rt = typejoin(rty, rt)
				#println("Callable $((mdef::Core.MethodMatch).method.sig), returning $rty, acc rty $rt")
				if argtuple <: mdef.method.sig
					has_candidate = true
				end
			end
			if has_candidate
				#println("Success calling $fn; returning $rt")
				ctx.octx.ledger[ctx.octx.node_mapping[loc]] = Dispatch(canonical_args, rt)
				return BasicType(rt)
			end
			# todo: check if there's an interface declared for this type
		end
		buff = IOBuffer()
		dump(buff, fn_rec)
		if isdefined(fn_rec, :instance)
			instance = fn_rec.instance
		else 
			instance = nothing 
		end
		output = """Invalid method call $fn_rec with args $canonical_args
			Searching for functions using signature $argtuple; attempts:
			$(join(["$(mdef.method.sig); argtuple <: typ?: $(argtuple <: mdef.method.sig)" for mdef in Iterators.take(directly_callable, 5)], "\n"))
		"""
	catch e 
		output = """Invalid method call $fn_rec with args $canonical_args
			Searching for functions using signature $argtuple; attempts:
			$(join(["$(mdef.method.sig); argtuple <: typ?: $(argtuple <: mdef.method.sig)" for mdef in Iterators.take(directly_callable, 5)], "\n"));
			encountered exception while dispatching $e
		"""
	end
	make_error(ctx.octx, loc, output, BasicType(rt))
end

function dispatch_intrinsic(fn::Core.Builtin, args::Vector{Any})
    world = ccall(:jl_get_tls_world_age, UInt, ())
    interp = Core.Compiler.NativeInterpreter(world)
	return BasicType(Core.Compiler.builtin_tfunction(interp, fn, args, nothing))
end

function typecheck_fn_call(lctx::LocalContext, inv::ASTNode, receiver::Expression, pos_args::Vector{PositionalArgs}, kw_args::Vector{Union{KeywordArg, SplatArg}})
	(ictx, rectyp) = typecheck_expression(lctx, receiver)
	(ictx, argtyps, kwtyps) = typecheck_fn_arguments(ictx, pos_args, kw_args)
	return typecheck_fn_call(ictx, inv, rectyp, argtyps, kwtyps)
end

is_fixed_splat(b::BasicType) = 
	b.type isa DataType && (b.type.name == Tuple.name || b.type.name == NamedTuple.body.body.name)
is_fixed_splat(_) = false

function typecheck_arguments(lctx::LocalContext, pos_args::Vector{PositionalArgs})
	argtyps = JlType[]
	for arg in pos_args
		@match arg begin
			PositionalArg(body, _) => begin
				(lctx, argty) = typecheck_expression(lctx, body)
				push!(argtyps, argty)
			end
			SplatArg(body, _) => begin 
				lctx, argty = typecheck_expression(lctx, body)
				splatted = []
				if is_fixed_splat(argty)
					splatted = BasicType.(collect(fieldtypes(canonize(argty))))
				elseif assignable(argty, BasicType(AbstractArray))
					make_error(lctx.octx, arg, "Variable-length splatting is not currently supported!")
				else 
					make_error(lctx.octx, arg, "Splatting of $argty is not allowed!")
				end
				append!(argtyps, splatted)
			end
		end
	end
	return (lctx, argtyps)
end

function typecheck_fn_arguments(ictx::LocalContext, pos_args::Vector{PositionalArgs}, kw_args::Vector{<:Union{KeywordArg, SplatArg}})
	kwtyps = Pair{Symbol, JlType}[]
	(ictx, argtyps) = typecheck_arguments(ictx, pos_args)
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
					make_error(ctx.octx, arg, "Variable-length splatting is not currently supported!")
				else 
					make_error(ctx.octx, arg, "Splatting of $argty is not allowed!")
				end
				append!(kwtyps, splatted)
			end
		end
	end
	return (ictx, argtyps, kwtyps)
end

function typecheck_fn_call(ictx::LocalContext, (@nospecialize inv::ASTNode), rectyp::JlType, pos_args::Vector{JlType}, kw_args::Vector{Pair{Symbol, JlType}})
	if length(kw_args) > 0
		if (!(rectyp.type isa DataType) || !isdefined(rectyp.type, :instance)) 
			return make_error(ictx.octx, inv, "Cannot make a kwargs invocation on a $rectyp-typed receiver", BasicType(Any))
		end
			
		func = Core.kwfunc(rectyp.type.instance)
		if length(methods(func)) == 0
			make_error(ictx.octx, inv, "$func is not a keywords function type")
			return typecheck_fn_call(ictx, inv, rectyp, pos_args, Pair{Symbol, JlType}[])
		end
		ntty = NamedTuple{(first.(kw_args)..., ), Tuple{canonize.(last.(kw_args))...}}
		res = dispatch_typed_direct(ictx, inv, typeof(func), Any[ntty; rectyp.type; canonize.(pos_args)])
		return (ictx, res)
	else 
		#println("making a function call onto $rectyp")
		if rectyp isa SpecialFunction
			res = dispatch_intrinsic(rectyp.fn, Any[ub_tyvar(canonize(arg)) for arg in pos_args])
		else
			#println("not a special function $rectyp $(typeof(rectyp)) $(pos_args) $(typeof.(pos_args))")
			res = dispatch_typed_direct(ictx, inv, canonize(rectyp), canonize.(pos_args))
		end
		return (ictx, res)
	end
end

#no I'm not proud
getproperty_helper(x::T, name::Val{Sym}) where {T, Sym} = getproperty(x, Sym)
typecheck_getproperty(ictx::LocalContext, (@nospecialize getprop::ASTNode), typ, prop::Union{Symbol, Literal}) = @match prop begin
	s::Symbol => (ictx, dispatch_typed_direct(ictx, getprop, typeof(getproperty_helper), [typ, Val{s}]))
	Literal(vl, _) => (ictx, dispatch_typed_direct(ictx, getprop, typeof(getproperty_helper), [typ, Val{vl}]))
end
typecheck_module_access(ictx::LocalContext, mod, prop::Union{Symbol, Literal}) = @match prop begin 
	s::Symbol => (ictx, spec_typeof(getproperty(mod, s)))
end

literal_typeof(e) = BasicType(typeof(e))
jlmeet(restys::Vector{JlType}) = BasicType(reduce(Base.typejoin, canonize.(restys); init=Union{}))

function typecheck_conditional(lctx::LocalContext, (@nospecialize cond::Expression))
	(lctx, condty) = typecheck_expression(lctx, cond)
	if !assignable(condty, BasicType(Bool)) && !assignable(condty, BasicType(Union{})) # we accept bottom to handle program flow control in conditionals
		println("failure from $cond")
		make_error(lctx.octx, cond, "Cannot use a nonboolean $condty in a conditional context")
	end
	return lctx
end
 
function add_end_token(ictx::LocalContext, arrty::JlType) 
	rctx = LocalContext(ictx)
	rctx.in_array = arrty
	return rctx 
end

typecheck_iterator(ctx::LocalContext, i::Iterspec) = @match i begin 
	IterEq(lhs::LValue, rhs::Expression, _) => begin 
		ictx, iterty = typecheck_expression(ctx, rhs)
		bind_argument(ictx, lhs, itertype(iterty))
	end
	Filter(inner::Vector{Iterspec}, cond::Expression, _) => begin 
		for inner_iter in inner 
			ctx = typecheck_iterator(ctx, inner_iter)
		end
		typecheck_conditional(ctx, cond)
	end
end

function typecheck_vcat_args(lctx::LocalContext, elems::Vector{<:Union{Row, Expression, Splat}})
	elemtys = JlType[]
	has_rows = false
	nrows = 0
	for elem in elems 
		@match elem begin 
			e::Expression => begin 
				(lctx, ity) = typecheck_expression(lctx, e)
				push!(elemtys, ity)
				nrows += 1
			end
			Row(relems, _) => begin 
				(lctx, itys, nrows, _) = typecheck_vcat_args(lctx, relems)
				append!(elemtys, itys)
				nrows += 1
				has_rows = true
			end
			Splat(ex::Expression, _) =>  begin 
				make_error(lctx.octx, cond, "Splatting in vcat/hcat not supported")
				return (lctx, [], 0)
			end
		end
	end
	return (lctx, elemtys, nrows, has_rows)
end

function typecheck_expression(lctx::LocalContext, expr::Expression)
	@match expr begin 
		Literal(expr::Any, _) => (lctx, literal_typeof(expr))
		Variable(:end, _) => !isnothing(lctx.in_array) ? 
			typecheck_fn_call(lctx, expr, BasicType(typeof(Base.lastindex)), JlType[lctx.in_array], Pair{Symbol, JlType}[]) : (lctx, lookup_variable_type(lctx, :end, binding))
		Variable(name::Symbol, _) => (lctx, lookup_variable_type(lctx, name, expr))
		FunctionDef(name::FunctionName, arguments::Vector{FnArg}, kw_args::Vector{KwArg}, sparams::Vector{TyVar}, rett::Union{Expression, Nothing}, body::Union{Expression, Nothing}, _) => 
			(lctx, typecheck_function(lctx.octx, get_scope_info(lctx.octx, expr), name, arguments, kw_args, sparams, rett, body))
		MacroDef(name::ResolvedName, arguments::Vector{FnArg}, sparams::Vector{TyVar}, rett::Union{Expression, Nothing}, body::Union{Expression, Nothing}, _) => 
			throw("not implemented")
		Block(exprs::Vector{Expression}, _) => begin 
			(lctx, rtty) = (lctx, BasicType(Nothing))
			for expr in exprs 
				res = typecheck_expression(lctx, expr)
				(lctx, rtty) = res
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
		Comparison(first::Expression, clauses::Vector{Pair{Expression, Expression}}, _) => begin 
			(lctx, ty1) = typecheck_expression(lctx, first)
			for clause in clauses 
				(lctx, ty2) = typecheck_expression(lctx, clause[2])
				func = @match clause[1] begin 
					Variable(x, _) => lookup_variable_type(lctx, Symbol(x), expr)
					_ => begin 
						make_error(lctx.octx, clause[1], "Can only use simple operators as comparisions within a comparison statement")
						continue
					end
				end
				(lctx, tyr) = typecheck_fn_call(lctx, expr, func, JlType[ty1, ty2], Pair{Symbol, JlType}[])
				if @match tyr begin BasicType(b) => b != Union{} && b != Bool; _ => false end
					make_error(lctx.octx, expr, "Component of comparison did not type check to a conditional value (bool or bottom)")
				end
				ty1 = ty2
			end
			return (lctx, BasicType(Bool))
		end
		SemanticAST.Broadcast(op::Expression, _) => (lctx, make_error(lctx.octx, expr, "Not implemented", BasicType(Any)))
		FunCall(Variable(:(&&) || :(||), _), [PositionalArg(l, _), PositionalArg(r, _)], _, _) => begin
			ictx = typecheck_conditional(lctx, l)
			(ictx, rty) = typecheck_expression(ictx, r)
			return (lctx, rty)
		end
		FunCall(SemanticAST.Broadcast(op::Expression, _), pos_args::Vector{PositionalArgs}, kw_args::Vector{Union{KeywordArg, SplatArg}}, _)&&fn => begin 
			(ictx, rectyp) = typecheck_expression(lctx, op)
			(ictx, argtyps, kwtyps) = typecheck_fn_arguments(ictx, pos_args, kw_args)
			return typecheck_fn_call(ictx, fn, BasicType(typeof(Base.broadcast)), [rectyp; argtyps], kwtyps)
		end
		SemanticAST.BroadcastAssignment(lhs::Expression, rhs::Expression, _)&&assignment => begin
			(ictx, ltyp) = typecheck_expression(lctx, lhs)
			(ictx, rtyp) = typecheck_expression(ictx, rhs)
			return typecheck_fn_call(ictx, assignment, BasicType(typeof(Base.broadcast!)), JlType[BasicType(typeof(Base.identity)); ltyp; rtyp], Pair{Symbol, JlType}[])
		end
		FunCall(receiver::Expression, pos_args::Vector{PositionalArgs}, kw_args::Vector{Union{KeywordArg, SplatArg}}, _)&&fn => begin 
			typecheck_fn_call(lctx, fn, receiver, pos_args, kw_args)
		end
		GetIndex(arr::Expression, arguments::Vector{PositionalArgs}, _) => begin 
			(lctx, arrty) = typecheck_expression(lctx, arr)
			ictx = add_end_token(lctx, arrty)
			(_, argtyps) = typecheck_arguments(ictx, arguments)
			return typecheck_fn_call(lctx, expr, BasicType(typeof(Base.getindex)), JlType[arrty; argtyps], Pair{Symbol, JlType}[])
		end
		GetProperty(rec::Expression, prop::Union{Symbol, Literal}, _) => begin
			ictx, recty = typecheck_expression(lctx, rec)
			@match recty begin 
				BasicType(typ) => return typecheck_getproperty(ictx, expr, typ, prop)
				ModuleType(md) => return typecheck_module_access(ictx, md, prop)
			end
			throw("not implemented $recty")
		end
		Assignment(FunctionAssignment(name::FunctionName, args_stmts::Vector{FnArg}, kwargs_stmts::Vector{KwArg}, sparams::Vector{TyVar}, rett::Union{Expression, Nothing}, _), body::Expression, _) => begin
			(lctx, typecheck_function(lctx.octx, get_scope_info(lctx.octx, expr), name, args_stmts, kwargs_stmts, sparams, rett, body))
		end
		Assignment(lhs::LValue, rhs::Expression, _) => begin 
			ictx, argty = typecheck_expression(lctx, rhs)
			(bind_argument(ictx, lhs, argty), argty)
		end
		Update(op::Symbol, lhs::LValue, rhs::Expression, _) => begin 
			(ictx, lty, _) = typecheck_lvalue(lctx, lhs, nothing)
			(ictx, rty) = typecheck_expression(ictx, rhs)
			return typecheck_fn_call(ictx, expr, lookup_variable_type(ictx, Symbol(string(op)[1:end-1]), expr), JlType[lty, rty], Pair{Symbol, JlType}[])
		end
		SemanticAST.BroadcastUpdate(op::Symbol, lhs::Expression, rhs::Expression, _)&&assignment => begin
			(ictx, ltyp) = typecheck_expression(lctx, lhs)
			(ictx, rtyp) = typecheck_expression(ictx, rhs)
			return typecheck_fn_call(ictx, assignment, BasicType(typeof(Base.broadcast!)), [lookup_variable_type(ictx, Symbol(string(op)[1:end-1]), expr); ltyp; ltyp; rtyp], kwtyps)
		end
		WhereType(type::Expression, vars::Vector{TyVar}, _) => throw("not implemented")
		Declaration(vars::Vector{VarDecl}, _) => begin 
			lastType = BasicType(Nothing)
			for var in vars 
				if !isnothing(var.value)
					(lctx, lastType) = typecheck_expression(lctx, var.value)
					lctx = bind_argument(lctx, var.binding, lastType)
				end
			end
			return (lctx, lastType)
		end
		DoStatement(func::Expression, arguments::Vector{FnArg}, body::Expression, _) => throw("not implemented")
		TupleExpr(exprs::Vector{Union{Expression, Splat}}, _) => begin
			tupletypes = JlType[]
			for expr in exprs 
				(lctx, rtty) = @match expr begin
					e::Expression => typecheck_expression(lctx, expr)
					s::Splat => throw("Splatting not currently supported!")
				end
				push!(tupletypes, rtty)
			end
			return (lctx, BasicType(Tuple{(canonize.(tupletypes))...}))
		end
		NamedTupleExpr(exprs::Vector{NamedTupleBody}, _) => throw("not implemented")
		StringInterpolate(components::Vector{Union{String, Expression}}, _) => begin
			for component in components
				(lctx, ity) = @match component begin 
					e::Expression => typecheck_expression(lctx, e)
					::String => (lctx, BasicType(String))
				end
			end
			return (lctx, BasicType(String))
		end
		TypeAssert(val::Expression, typ::Expression, _) => begin 
			(lctx, _) = typecheck_expression(lctx, val)
			(lctx, convert_type(lctx, typ))
		end
		IfStmt(clauses::Vector{IfClause}, _) => begin
			restys = JlType[]
			for clause in clauses 
				ictx = lctx
				if !isnothing(clause.cond)
					ictx = typecheck_conditional(ictx, clause.cond)
				end
				(_, resty) = typecheck_expression(ictx, clause.body)
				push!(restys, resty)
			end
			return (lctx, jlmeet(restys))
		end
		WhileStmt(cond::Expression, body::Expression, _) => begin
			lctx = typecheck_conditional(lctx, cond)
			(_, bodyty) = typecheck_expression(lctx, body)
			return (lctx, BasicType(Nothing))
		end
		BreakStmt(_) => return (lctx, BasicType(Union{}))
		ContinueStmt(_) => return (lctx, BasicType(Union{}))
		ReturnStmt(retval::Union{Expression, Nothing}, _) => isnothing(retval) ? (add_return(lctx, retval, BasicType(Nothing)), BasicType(Nothing)) : let (lctx, rtty) = typecheck_expression(lctx, retval); (add_return(lctx, retval, rtty), BasicType(Union{})) end
		ForStmt(iters::Vector{Pair{LValue, Expression}}, body::Expression, _) => begin 
			inner_ctx = lctx
			for (lvalue, iter) in iters 
				(inner_ctx, iterty) = typecheck_expression(inner_ctx, iter)
				inner_ctx = bind_argument(inner_ctx, lvalue, itertype(iterty))
			end
			(_, _) = typecheck_expression(inner_ctx, body)
			(lctx, BasicType(Nothing))
		end
		Vect(elems::Vector{Union{Expression, Splat}}, _) => begin
			elemty = BasicType(Union{})
			for elem in elems 
				@match elem begin 
					e::Expression => begin 
						(lctx, ity) = typecheck_expression(lctx, e)
						elemty = typemeet(ity, elemty)
					end
					Splat(ex::Expression, _) =>  begin 
						(lctx, ity) = typecheck_expression(lctx, e)
						elemty = typemeet(itertype(ity), elemty)
					end
				end
			end
			(lctx, BasicType(Vector{canonize(elemty)}))
		end
		HCat(type::Union{Expression, Nothing}, elems::Vector{Union{Expression, Splat}}, _) => begin
			elemtys = JlType[]
			for elem in elems 
				@match elem begin 
					e::Expression => begin 
						(lctx, ity) = typecheck_expression(lctx, e)
						push!(elemtys, ity)
					end
					Splat(ex::Expression, _) =>  begin 
						(lctx, ity) = typecheck_expression(lctx, e)
						push!(elemtys, itertype(ity))
					end
				end
			end
			typecheck_fn_call(lctx, expr, BasicType(typeof(Base.hcat)), elemtys, Pair{Symbol, JlType}[])
		end
		VCat(type::Union{Expression, Nothing}, rows::Vector{Union{Row, Expression, Splat}}, _) => begin
			(lctx, elemtys, nrows, has_rows) = typecheck_vcat_args(lctx, rows)
			if !has_rows
				typecheck_fn_call(lctx, expr, BasicType(typeof(Base.vcat)), elemtys, Pair{Symbol, JlType}[])
			else 
				typecheck_fn_call(lctx, expr, BasicType(typeof(Base.hvcat)), JlType[BasicType(Tuple{repeat([Int], nrows)...}); elemtys], Pair{Symbol, JlType}[])
			end
		end
		NCat(type::Union{Expression, Nothing}, dim::Int, rows::Vector{Union{NRow, Expression}}, _) => (lctx, make_error(lctx.octx, expr, "Not implemented!", BasicType(Any)))
		Generator(flatten::Bool, expr::Expression, iterators::Vector{Iterspec}, _) && gen => throw("Standalone generators are not currently supported; use a comprehension instead")
		Comprehension(type::Union{Expression, Nothing}, gen::Generator, _)&&cmp => begin 
			ictx = lctx
			is_flat = gen.flatten || any(iter -> iter isa Filter, gen.iterators)
			if is_flat 
				dim = 1
			else 
				dim = length(gen.iterators)
			end
			for iter in gen.iterators 
				ictx = typecheck_iterator(ictx, iter)
			end
			(_, elty) = typecheck_expression(ictx, gen.expr)
			if !isnothing(type)
				tgt_type = convert_type(lctx, type)
				if !assignable(elty, tgt_type)
					make_error(lctx.octx, gen.expr, "Comprehension body returns $(elty) while expecting $tgt_type.")
				end
				elty = tgt_type
			end
			(lctx, BasicType(Array{canonize(elty), dim}))
		end
		Quote(ast::JuliaSyntax.SyntaxNode, _) => begin 
			JuliaSyntax.kind(JuliaSyntax.head(ast)) == JuliaSyntax.K"quote" && typeof(JuliaSyntax.Expr(JuliaSyntax.child(ast, 1))) == Symbol ? (lctx, BasicType(Symbol)) : (lctx, BasicType(Expr)) # todo
		end
		MacroExpansion(value::Any, _) => throw("not implemented")
		Ternary(cond::Expression, then::Expression, els::Expression, _) => begin
			restys = JlType[]
			ictx = typecheck_conditional(lctx, cond)
			(_, t1) = typecheck_expression(ictx, then)
			(_, t2) = typecheck_expression(ictx, els)
			return (ictx, jlmeet(JlType[t1, t2]))
		end
	end
end

typecheck(ctx::TypecheckContext, expr::SemanticAST.ToplevelStmts) = @match expr begin
    ToplevelStmt(exprs, _) => typecheck.((ctx, ), exprs)
    ModuleStmt(std_imports, name, body, _) && m => typecheck.((ctx, ), body)
	ExprStmt(FunctionDef(name, arguments, kwargs, sparams, rett, body, _), _) => typecheck_function(ctx, get_scope_info(ctx, expr), name, arguments, kwargs, sparams, rett, body)
	ExprStmt(Assignment(FunctionAssignment(name::FunctionName, args_stmts::Vector{FnArg}, kwargs_stmts::Vector{KwArg}, sparams::Vector{TyVar}, rett::Union{Expression, Nothing}, _), body::Expression, _), _) => typecheck_function(ctx, get_scope_info(ctx, expr), name, args_stmts, kwargs_stmts, sparams, rett, body)
    _ => begin println(expr); end
end
