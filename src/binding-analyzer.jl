abstract type JType end

struct TypeVarDef
	lb::JType
	var::Symbol
	ub::JType
end
@as_record TypeVarDef

@data TypeLitValue begin
	TypeTypeLit(JType)
	ValueTypeLit(Any)
end

const NamePath = Vector{Symbol}
@data JuliaType <: JType begin
	NominalType(NamePath, Vector{JuliaType})
	TupleType(Vector{JuliaType})
	UnionType(Vector{JuliaType})
	AnyType()
	UnionAllType(JuliaType, Vector{TypeVarDef})
	TypeVarType(Symbol)
	TypeLitType(TypeLitValue)
end
@generated function Base.:(==)(a::T, b::T) where T<:Union{JType, TypeVarDef}
	if length(fieldnames(T)) == 0 
		return true
	end
	return :(Base.:(&)($(map(x->:(a.$x == b.$x), fieldnames(T))...)))
end

abstract type Definition end
abstract type ScopeDefinition <: Definition end

mutable struct ToplevelContext
	parent::Union{ToplevelContext, Nothing}
	bindings::Base.ImmutableDict{Symbol, Definition}
	search::Vector{ScopeDefinition}
	exports::Vector{Symbol}
end
root_context(t::ToplevelContext) = isnothing(t.parent) ? t : root_context(t.parent)

struct ValueDefinition <: Definition
	source::Entity
end
struct TypeDefinition <: Definition
	source::Entity
	fields::Dict{Symbol, JuliaType}
	extensible::Bool
end
struct ModuleDefinition <: ScopeDefinition
	source::Entity
	ctx::ToplevelContext
end
struct SymbolServerDefinition <: ScopeDefinition
	source::Entity
	store::SymbolServer.ModuleStore
end

make_extensible(::Definition) = nothing
make_extensible(t::TypeDefinition) = t.extensible = true

Base.haskey(l::ModuleDefinition, n::Symbol) = haskey(l.ctx, n)
Base.haskey(t::ToplevelContext, n::Symbol) = n in keys(t.bindings)
Base.getindex(s::ToplevelContext, n::Symbol) = s.bindings[n]
Base.getindex(s::SymbolServerDefinition, n::Symbol) = s.store[n]
Base.getindex(l::ModuleDefinition, n::Symbol) = l.ctx[n]
Base.getindex(d::ScopeDefinition, n::Vector{Symbol}) = 
	if length(n) == 1 
		d[n[1]]
	else 
		d[last(n)][n[1:end-1]]
	end


bind_function_name(ctx::TypecheckContext, tctx::ToplevelContext, name::FunctionName) = @match name begin
	ResolvedName(path::Vector{Symbol}, loc) => 
		if length(path) == 1 && !haskey(tctx.bindings, first(path))
			tctx.bindings = Base.ImmutableDict(tctx.bindings, first(path) => TypeDefinition(ctx.node_mapping[name], Dict{Symbol, JuliaType}(), true))
		end
	DeclName(binding::Union{LValue, Nothing}, typ::Expression, loc) => nothing
	TypeFuncName(receiver::Expression, args::Vector{Union{Expression, TyVar}}, loc) => nothing
	AnonFuncName(loc) => nothing
end
analyze_toplevel_lvalue(ctx::TypecheckContext, tctx::ToplevelContext, expr::SemanticAST.LValue) = @match expr begin 
	IdentifierAssignment(id::Symbol, loc) => begin tctx.bindings = Base.ImmutableDict(tctx.bindings, id=>ValueDefinition(ctx.node_mapping[expr])) end
	OuterIdentifierAssignment(id::Symbol, loc) => nothing
	FieldAssignment(obj::Expression, name::Symbol, loc) => nothing
	TupleAssignment(params::Vector{LValue}, loc) => map(param -> analyze_toplevel_lvalue(ctx, tctx, param), params)
	RefAssignment(arr::Expression, arguments::Vector{PositionalArgs}, kwargs::Vector{KeywordArg}, loc) => nothing
	VarargAssignment(tgt::Union{Nothing, LValue}, loc) => nothing
	TypedAssignment(lhs::LValue, type::Expression, loc) => analyze_toplevel_lvalue(ctx, tctx, lhs)
	NamedTupleAssignment(params::Vector{Union{IdentifierAssignment, TypedAssignment}}, loc) => map(param->analyze_toplevel_lvalue(param), params)
	FunctionAssignment(name::FunctionName, args_stmts::Vector{FnArg}, kwargs_stmts::Vector{KwArg}, sparams::Vector{TyVar}, rett::Union{Expression, Nothing}, loc) => 
		bind_function_name(ctx, tctx, name)
    UnionAllAssignment(name::LValue, tyargs::Vector{TyVar}, loc) => analyze_toplevel_lvalue(ctx, tctx, name)
end
analyze_bindings(ctx::TypecheckContext, tctx::ToplevelContext, expr::SemanticAST.ToplevelStmts) = @match expr begin
    ToplevelStmt(exprs, _) => foldl((tctx, exp) -> analyze_bindings(ctx, tctx, exp), exprs; init=tctx)
    ModuleStmt(std_imports, name, body, _) && m => 
    	let ictx = ToplevelContext(tctx, Base.ImmutableDict{Symbol, Definition}(), [], []);
    	tctx.bindings = Base.ImmutableDict(tctx.bindings, name => 
    		ModuleDefinition(ctx.node_mapping[m], foldl((tctx, exp) -> analyze_bindings(ctx, tctx, exp), body; init=ictx)));
    	tctx
    	end
    UsingStmt(paths, _) => foldl((tctx, path) -> analyze_using(ctx, tctx, path), paths; init=tctx)
    ImportStmt(paths, _) => foldl((tctx, path) -> analyze_import(ctx, tctx, path), paths; init=tctx)
    SourceUsingStmt(source, paths, _) => foldl((tctx, path) -> analyze_using(l, source, path), paths; init=tctx)
    SourceImportStmt(source, paths, _) => foldl((tctx, path) -> analyze_import(l, source, path), paths; init=tctx)
    ExportStmt(syms, _) => foldl((tctx, exp) -> analyze_export(tctx, exp), syms; init=tctx)
    ExprStmt(Assignment(lvalue, value, il), _) => analyze_toplevel_lvalue(ctx, tctx, lvalue)
    ExprStmt(FunCall(Variable(:include, _), [PositionalArg(StringInterpolate([filepath], _), _)], _, _), _) => 
        let includefile = ctx.ledger[ctx.node_mapping[expr]][IncludeFile];
            new_root = includefile.include;
            new_ast = ctx.ledger[new_root][ASTComponent].node
            analyze_bindings(ctx, tctx, new_ast)
        end
    _ => begin println(expr); return tctx end
end


resolve_path(ctx::TypecheckContext, tctx::ToplevelContext, path::ImportPath) = @match path begin
       ImportField(source::ImportPath, name::Symbol, _) => resolve_path(ctx, scope, source)[name]
       ImportId(name::Symbol, _) => SymbolServerReference(ctx.node_mapping[path], ctx.store[name])
       ImportRelative(levels::Int, _) => LocalReference(foldl((pkg, _) -> 
       	if isnothing(pkg.parent)
       		make_error(ctx, path)
       		pkg
       	else
       		pkg.parent
       	end, enumerate(levels); init=tctx))
end

resolve_path(ctx::TypecheckContext, bnd::ScopeDefinition, path::ImportPath) = @match path begin
       ImportField(source::ImportPath, name::Symbol, _) => resolve_path(ctx, bnd, source)[name]
       ImportId(name::Symbol, _) => bnd[name]
       ImportRelative(levels::Int, _) => begin make_error(ctx, path); bnd end
end

inferred_name(path::ImportPath) = @match path begin
   ImportField(source::ImportPath, name::Symbol, _) => name
   ImportId(name::Symbol, _) => name
   ImportRelative(levels::Int, _) => nothing
end

function analyze_using(ctx::TypecheckContext, tctx::ToplevelContext, path::ImportPath)
	resolved = resolve_path(ctx, tctx, path)
	tctx.bindings = Base.ImmutableDict{Symbol, Definition}(tctx.bindings, inferred_name(path) => resolved)
	push!(tctx.search, resolved)
	tctx
end

analyze_import(ctx::TypecheckContext, tctx::ToplevelContext, path::DepClause) = @match path begin
    Dep(import_path, _) => begin
		resolved = resolve_path(ctx, tctx, import_path)
		tctx.bindings = Base.ImmutableDict{Symbol, Definition}(tctx.bindings, inferred_name(import_path) => resolved)
		return tctx
	end
    AliasDep(import_path, name, _) => begin
		resolved = resolve_path(ctx, tctx, import_path)
		tctx.bindings = Base.ImmutableDict{Symbol, Definition}(tctx.bindings,  name => resolved)
		return tctx
    end
end

analyze_common_reference(ctx::TypecheckContext, tctx::ToplevelContext, source_path::ImportPath, using_path::ImportPath, force_name::Union{Nothing, Symbol}=nothing, extensible::Bool=false) =
    begin 
    	def = resolve_path(ctx, resolve_path(ctx, tctx, source_path), using_path)
    	tctx.bindings = Base.ImmutableDict{Symbol, Definition}(tctx.bindings, inferred_name(using_path) => extensible ? make_extensible(def) : def)
    	tctx
    end
analyze_using(ctx::TypecheckContext, source_path::ImportPath, path::DepClause, can_extend=false) = @match path begin
    Dep(import_path, _) => analyze_common_reference(ctx, scope, path, source_path, import_path, nothing, can_extend)
    AliasDep(import_path, name, _) => analyze_common_reference(ctx, scope, path, source_path, import_path, name, can_extend)
end
analyze_import(ctx::TypecheckContext, basepath::ImportPath, path::DepClause) = analyze_using(ctx, scope, basepath, path, true)