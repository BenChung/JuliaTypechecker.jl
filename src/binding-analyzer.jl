@component struct Reference
    binding::Entity 
end

struct ImportedDefinition <: SourceInfo 
    path::Path
    extensible::Bool
end
struct ModuleReference <: SourceInfo
    path::Path
    searched::Bool
end

struct ToplevelDefinition <: SourceInfo
end
struct LocalDefinition <: SourceInfo
end
struct FunctionDefinition <: SourceInfo
end


const Scope = Base.ImmutableDict
empty_scope() = Scope{Symbol, Binding}()

get_scopeinfo(l::TypecheckContext, path::Path) = get_scopeinfo(l, l.root_scope, path)
function get_scopeinfo(l::TypecheckContext, scope::ScopeInfo, path::Path)
    if length(path) == 0 return scope end
    if haskey(scope.definitions, first(path))
        binding = scope.definitions[first(path)]
        if binding.source isa ModuleDefinition
            return get_scopeinfo(l, binding.source.local_scope, path[2:end])
        elseif binding.source isa ModuleReference
            # what to do here?
        end
        raise("missing module $(path)")
    else 

    end
end

function toplevel_bind(l::TypecheckContext, name::Symbol, at::ASTNode, src::SourceInfo)
    binding = Binding(at.location, src)
    l.ledger[l.node_mapping[at]] = binding

    scope = find_parent_component(ScopeInfo, l, at)
    scope.definitions[name] = binding
    return binding
end

function local_bind(l::TypecheckContext, lctx::Scope, name::Symbol, at::ASTNode, src::SourceInfo)
    binding = Binding(at.location, src)
    l.ledger[l.node_mapping[at]] = binding
    return LocalScope(lctx, name=>binding)
end

function toplevel_bind_function(ctx::TypecheckContext, bctx::ScopeInfo, name::FunctionName, info::SourceInfo)
    @match name begin 
        ResolvedName(path::Vector{Symbol}, _) =>
            if length(path) == 1
                toplevel_bind(l, path[1], name, info)
            else 

            end
        DeclName(binding::Union{LValue, Nothing}, typ::Expression, _) =>
        TypeFuncName(receiver::Expression, args::Vector{Union{Expression, TyVar}}, _) =>
        AnonFuncName(_) =>
    end
end

analyze_toplevel_lvalue(ctx::TypecheckContext, bctx::ScopeInfo, lctx::Scope, lvalue::LValue) = @match lvalue begin 
	IdentifierAssignment(id::Symbol, _) => id => toplevel_bind(ctx, id, lvalue, ToplevelDefinition())
	OuterIdentifierAssignment(id::Symbol, _) => make_error(ctx, lvalue, "Invalid outer assignment at top level") 
	FieldAssignment(obj::Expression, name::Symbol, l) => lctx
	TupleAssignment(params::Vector{LValue}, _) => foldl((lenv, exp)->analyze_toplevel_lvalue(ctx, benv, lenv, lctx), params; init=lctx)
	RefAssignment(arr::Expression, arguments::Vector{PositionalArgs}, kwargs::Vector{KeywordArg}, l) => lctx
	VarargAssignment(tgt::Union{Nothing, LValue}, l) => lctx
	TypedAssignment(lhs::LValue, type::Expression, _) => analyze_toplevel_lvalue(ctx, bctx, lctx, lhs)
	NamedTupleAssignment(params::Vector{Union{IdentifierAssignment, TypedAssignment}}, _) => analyze_toplevel_lvalue.((ctx, ), (lctx, ), params)
	FunctionAssignment(name::FunctionName, args_stmts::Vector{FnArg}, kwargs_stmts::Vector{KwArg}, sparams::Vector{TyVar}, rett::Union{Expression, Nothing}, _) =>
        throw("Unimplemented") # todo implement local/nonlocal function definitions
	BroadcastAssignment(lhs::LValue, l) => lctx
    UnionAllAssignment(name::LValue, tyargs::Vector{TyVar}, _) => 
        let lenv = foldl((lctx, el) -> local_bind(ctx, lctx, el.name, el, LocalDefinition()), tyargs; init=lctx)
            analyze_toplevel_lvalue(ctx, bctx, lctx, name)
        end
end


analyze_bindings(l::TypecheckContext, binding_scope::ScopeInfo, expr::SemanticAST.ToplevelStmts) = @match expr begin 
    ToplevelStmt(exprs, _) => map(exp -> analyze_bindings(l, binding_scope, exp), exprs)
    ModuleStmt(std_imports, name, body, _) && m => map(exp -> analyze_bindings(l, binding_scope, exp), body)
    UsingStmt(paths, _) => map(path -> analyze_using(l, binding_scope, path), paths)
    ImportStmt(paths, _) => map(path -> analyze_import(l, binding_scope, path), paths)
    SourceUsingStmt(source, paths, _) => map(path -> analyze_using(l, binding_scope, source, path), paths)
    SourceImportStmt(source, paths, _) => map(path -> analyze_import(l, binding_scope, source, path), paths)
    ExportStmt(syms, _) => push!.((scope.exports,), analyze_export.(syms))
    ExprStmt(Assignment(lvalue, value, il), _) => analyze_toplevel_lvalue(l, binding_scope, LocalScope{Symbol, Binding}(), lvalue)
    _ => println(expr)
end

inferred_name(path) = last(path)

resolve_path(ctx::TypecheckContext, scope::ScopeInfo, path::ImportPath) = @match path begin 
	ImportField(source::ImportPath, name::Symbol, _) => [resolve_path(ctx, scope, source); name]
	ImportId(name::Symbol, _) => [name]
	ImportRelative(levels::Int, _) =>
        if length(scope.path) >= levels
            scope.path[1:end-levels]
        else
            make_error(ctx, path, "Invalid relative path")
            return scope.path
        end
end

analyze_using(ctx::TypecheckContext, scope::ScopeInfo, path::ImportPath) = let 
    binding = Binding(path.location, ModuleReference(resolve_path(ctx, scope, path), true));
        ctx.ledger[ctx.node_mapping[path]] = binding
        scope.definitions[inferred_name(resolved)] = binding
    end

analyze_import(ctx::TypecheckContext, scope::ScopeInfo, path::DepClause) = @match path begin 
    Dep(import_path, _) => begin 
        binding = Binding(path.location, ModuleReference(resolve_path(ctx, scope, import_path), false))
        ctx.ledger[ctx.node_mapping[path]] = binding
        scope.definitions[inferred_name(resolved)] = binding
    end
    AliasDep(import_path, name, _) => begin
        binding = Binding(path.location, ModuleReference(resolve_path(ctx, scope, import_path), false)) 
        ctx.ledger[ctx.node_mapping[path]] = binding
        scope.definitions[name] = binding
    end
end

analyze_common_reference(ctx::TypecheckContext, scope::ScopeInfo, expr::ASTNode, source_path::ImportPath, using_path::ImportPath, force_name::Union{Nothing, Symbol}=nothing, extensible::Bool=false) = 
    begin 
        resolved = [resolve_path(ctx, scope, source_path); resolve_path(ctx, scope, using_path)];
        binding = Binding(using_path.location, ImportedDefinition(resolved, extensible))
        ctx.ledger[ctx.node_mapping[expr]] = binding
        scope.definitions[isnothing(force_name) ? inferred_name(resolved) : force_name] = binding
    end
analyze_using(ctx::TypecheckContext, scope::ScopeInfo, source_path::ImportPath, path::DepClause, can_extend=false) = @match path begin 
    Dep(import_path, _) => analyze_common_reference(ctx, scope, path, source_path, import_path, nothing, can_extend)
    AliasDep(import_path, name, _) => analyze_common_reference(ctx, scope, path, source_path, import_path, name, can_extend)
end
analyze_import(ctx::TypecheckContext, scope::ScopeInfo, basepath::ImportPath, path::DepClause) = analyze_using(ctx, scope, basepath, path, true)

analyze_export(sym) = sym
