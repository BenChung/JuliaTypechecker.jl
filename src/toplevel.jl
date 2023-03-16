node_mapping = Dict{ASTNode, Entity}()
@component struct ASTComponent
    node::Union{ASTNode, Symbol}
    parent::Union{Entity, Nothing}
end
@component struct Positioned 
    position::SourcePosition
end

function analyze_file(c::TypecheckContext, file::String)::Entity
    ast = SemanticAST.expand_toplevel(JuliaSyntax.parseall(JuliaSyntax.SyntaxNode, input), ExpandCtx(true, false))
    to_entities(c, ast, nothing)
    #to_entities(c, ast, nothing)
end

function to_entities(m::TypecheckContext, e, parent::Union{Entity, Nothing})
    function enter(c)
        if !(c isa ASTNode)
            if !(c isa Symbol || c isa Real || c isa Nothing)
                println(typeof(c))
            end
            return
        end
        node = Entity(m.ledger)
        m.node_mapping[c] = node
        m.ledger[node] = ASTComponent(c, parent)
        parent = node
    end
    function exit(c)
        if !haskey(m.node_mapping, c)
            return
        end
        node = m.node_mapping[c]
        if ASTComponent in m.ledger[node]
            component = m.ledger[node][ASTComponent]
            parent=component.parent
        end
    end
    SemanticAST.visit(enter, exit, e)
end
