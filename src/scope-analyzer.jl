@component struct IncludeFile
    file::String
    include::Entity
end
@component struct InFile
    path::String
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
    if !has_file(l.file_resolver, current_file, filename)
        return nothing
    end
    expr = JuliaSyntax.parseall(JuliaSyntax.SyntaxNode, load_file(l.file_resolver, current_file, filename))
    ast = expand_toplevel(expr, ExpandCtx(true, false))
    to_entities(l, ast, nothing)
    
    root_entity = l.node_mapping[ast]
    push!(scope.children, root_entity)

    root = l.ledger[root_entity]
    module_scope = ScopeInfo(scope.path, root, scope.root, []) # m.std_imports ? [] : [],
    fullpath = joinpath(dirname(current_file), filename)
    l.ledger[root_entity] = module_scope
    l.ledger[root_entity] = InFile(fullpath)

    analyze_scope(l, path, module_scope, ast)
    return IncludeFile(fullpath, root_entity)
end

make_error(ctx::TypecheckContext, node) = ctx.ledger[ctx.node_mapping[node]] = TypeError()
analyze_scope(l::TypecheckContext, path, scope::ScopeInfo, expr::SemanticAST.ToplevelStmts) = @match expr begin 
    ToplevelStmt(exprs, _) => analyze_scope.((l, ), (path, ), (scope, ), exprs)
    ModuleStmt(std_imports, name, body, _) && m => analyze_module!(l, scope, m, path)
    ExprStmt(FunCall(Variable(:include, _), [PositionalArg(StringInterpolate([filepath], _), _)], _, _), _) => 
        let infile = find_parent_component(InFile, l, expr);
            imported = resolve_import(l, path, scope, infile.path, filepath);
            if !isnothing(imported)
                l.ledger[l.node_mapping[expr]] = imported
            else
                l.ledger[l.node_mapping[expr]] = TypeError() 
            end
        end
    _ => nothing # println(expr)
end

function analyze_module!(l::TypecheckContext, scope::ScopeInfo, m::ModuleStmt, path)
    module_path = [path; m.name]
    root = l.ledger[l.node_mapping[m]]
    module_scope = ScopeInfo(module_path, root, nothing, []) # m.std_imports ? [] : [],
    l.ledger[l.node_mapping[m]] = module_scope
    analyze_scope.((l, ), (module_path,), (module_scope, ), m.body)
end
