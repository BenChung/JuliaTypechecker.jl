@component struct IncludeFiles
    file::String
    includes::Vector{Pair{String, Entity}}
end

struct Binding
    location::SemanticAST.SourcePosition
    source::SourceInfo
end

@component struct TypeError 
    message::String
end

struct ModuleDefinition <: SourceInfo
    local_scope::ScopeInfo
end

function make_error(ctx::TypecheckContext, element::ASTNode, msg::String) 
    ctx.ledger[ctx.node_mapping[element]] = TypeError(msg)
end

function get_definition(c::TypecheckContext, s::ScopeInfo, l::Symbol)
	if l in keys(s.definitions)
		return s.definitions[l]
	end
	if !isnothing(s.parent)
		return get_definition(c, c.ledger[ScopeInfo][s.parent], l)
	end
	return get_definition_descending(c, s, l)
end

function get_definition_descending(c::TypecheckContext, s::ScopeInfo, l::Symbol)
	if l in keys(s.definitions)
		return s.definitions[l]
	end
	for child in s.children
		child_def = get_definition_descending(c, c.ledger[ScopeInfo][child], l)
		if !isnothing(child_def) 
			return child_def
		end
	end
	return nothing
end

find_parent_component(t, l::TypecheckContext, expr::ASTNode) = find_parent_component(t, l, l.node_mapping[expr])
function find_parent_component(t, l::TypecheckContext, expr::Entity)
    if expr in l.ledger[t]
        return l.ledger[t][expr]
    end
    astcomponent = l.ledger[ASTComponent][expr]
    if !isnothing(astcomponent.parent)
        return find_parent_component(t, l, astcomponent.parent)
    else 
        return nothing
    end
end

function resolve_import(l::TypecheckContext, path::Path, scope::ScopeInfo, current_file, filename)
    expr = JuliaSyntax.parseall(JuliaSyntax.SyntaxNode, load_file(l.file_resolver, current_file, filename))
    ast = expand_toplevel(expr, ExpandCtx(true, false))
    to_entities(l, ast, nothing)
    
    root_entity = l.node_mapping[ast]
    push!(scope.children, root_entity)

    root = l.ledger[root_entity]
    module_scope = ScopeInfo(scope.path, root, scope.root, [], Dict{Symbol, Binding}(), Set{Symbol}()) # m.std_imports ? [] : [],
    l.ledger[root_entity] = module_scope
    l.ledger[root_entity] = IncludeFiles(joinpath(dirname(current_file), filename), Vector{Pair{String, Entity}}())

    analyze_scope(l, path, module_scope, ast)
    return root_entity
end

analyze_scope(l::TypecheckContext, path, scope::ScopeInfo, expr::SemanticAST.ToplevelStmts) = @match expr begin 
    ToplevelStmt(exprs, _) => analyze_scope.((l, ), (path, ), (scope, ), exprs)
    ModuleStmt(std_imports, name, body, _) && m => analyze_module!(l, scope, m, path)
    ExprStmt(FunCall(Variable(:include, _), [PositionalArg(StringInterpolate([filepath], _), _)], _, _), _) => 
    push!(find_parent_component(IncludeFiles, l, expr).includes, 
        let infile = find_parent_component(IncludeFiles, l, expr);
            filepath => resolve_import(l, path, scope, infile.file, filepath)
        end
    ) # todo
    _ => nothing # println(expr)
end

function analyze_module!(l::TypecheckContext, scope::ScopeInfo, m::ModuleStmt, path)
    module_path = [path; m.name]
    root = l.ledger[l.node_mapping[m]]
    module_scope = ScopeInfo(module_path, root, nothing, [], Dict{Symbol, Binding}(), Set{Symbol}()) # m.std_imports ? [] : [],
    l.ledger[l.node_mapping[m]] = module_scope
    infile = find_parent_component(IncludeFiles, l, m)
    l.ledger[l.node_mapping[m]] = IncludeFiles(infile.file, Vector{Pair{String, Entity}}())

    scope.definitions[m.name] = Binding(m.location, ModuleDefinition(module_scope))
    analyze_scope.((l, ), (module_path,), (module_scope, ), m.body)
end



#=
stmt = SemanticAST.expand_toplevel(JuliaSyntax.parseall(JuliaSyntax.SyntaxNode, "import Foo; using Baz.Bar; using Bing.Bar.Blah"), ExpandCtx(true, false))
toplevel_scope = ScopeInfo([:Main], Vector{Path}[], Dict{Symbol, Binding}(), Set{Symbol}())
analyze_scope([:Main], toplevel_scope, stmt)
toplevel_scope

stmt = SemanticAST.expand_toplevel(JuliaSyntax.parseall(JuliaSyntax.SyntaxNode, "import Foo; module Baz end"), ExpandCtx(true, false));
toplevel_scope = ScopeInfo([:Main], Vector{Path}[], Dict{Symbol, Binding}(), Set{Symbol}());
analyze_scope([:Main], toplevel_scope, stmt);
toplevel_scope;

stmt = SemanticAST.expand_toplevel(JuliaSyntax.parseall(JuliaSyntax.SyntaxNode, "import Foo; include(\"example.jl\")"), ExpandCtx(true, false));
toplevel_scope = ScopeInfo([:Main], Vector{Path}[], Dict{Symbol, Binding}(), Set{Symbol}());
analyze_scope([:Main], toplevel_scope, stmt);
toplevel_scope;
=#