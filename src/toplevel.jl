node_mapping = Dict{ASTNode, Entity}()
@component struct ASTComponent
    node::Union{ASTNode, Symbol}
    parent::Union{Entity, Nothing}
end
@component struct Name
    name::Symbol
end
@component struct Positioned 
    position::SourcePosition
end

function analyze_file(c::TypecheckContext, file::String)::Entity
    ast = SemanticAST.expand_toplevel(JuliaSyntax.parseall(JuliaSyntax.SyntaxNode, input), ExpandCtx(true, false))
    to_entities_new(c, ast, nothing)
    #to_entities(c, ast, nothing)
end

function to_entities(m::TypecheckContext, e, parent::Union{Entity, Nothing})
    SemanticAST.visit(c -> begin
        if c isa Symbol
            node = Entity(m.ledger)
            m.ledger[node] = Name(c)
            return
        end
        if !(c isa ASTNode) 
            return
        end
        node = Entity(m.ledger)
        m.node_mapping[c] = node
        m.ledger[node] = ASTComponent(c, parent)
        parent = node
    end, c->begin
        if !haskey(m.node_mapping, c)
            return
        end
        node = m.node_mapping[c]
        if ASTComponent in m.ledger[node]
            component = m.ledger[node][ASTComponent]
            parent = component.parent
        end
    end, e)
end
