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
        ast = to_entities(m, SemanticAST.expand_toplevel(JuliaSyntax.parseall(JuliaSyntax.SyntaxNode, input), ExpandCtx(true, false)), nothing)
end

function make_node(m::TypecheckContext, l::SourcePosition, a::ASTNode, f::Function)
    e = Entity(m.ledger)
    m.node_mapping[a] = e
    m.ledger[e] = Positioned(l)
    f(e)
    return e
end
optional_array(el::Nothing) = []
optional_array(x) = [x]
function to_entities(m::TypecheckContext, s::Symbol, parent::Union{Entity, Nothing} = nothing)
    e = Entity(m.ledger)
    m.ledger[e] = Name(s)
    return e
end
to_entities(m::TypecheckContext, a::ToplevelStmts, parent::Union{Entity, Nothing} = nothing) = @match a begin
    StructDefStmt(name::Symbol, params::Vector{Symbol}, super::Union{Expression, Nothing}, fields::Vector{StructField}, cstrs::Vector{Expression}, l) => 
        to_entities.((m, ), [name; params; optional_array(super); fields; cstrs], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
    AbstractDefStmt(name::Symbol, params::Vector{Symbol}, super::Union{Expression, Nothing}, l) => 
        to_entities.((m, ), [name; params; optional_array(super)], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
    PrimitiveDefStmt(name::Symbol, params::Vector{Symbol}, super::Union{Expression, Nothing}, size::Expression, l) => 
        to_entities.((m, ), [name; params; optional_array(super)], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
    UsingStmt(mods::Vector{ImportPath}, l) => 
        to_entities.((m, ), mods, (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
    ImportStmt(mods::Vector{DepClause}, l) => 
        to_entities.((m, ), mods, (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
    SourceUsingStmt(sourcemod::ImportPath, stmts::Vector{DepClause}, l) => 
        to_entities.((m, ), [sourcemod; stmts], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
    SourceImportStmt(sourcemod::ImportPath, stmts::Vector{DepClause}, l) => 
        to_entities.((m, ), [sourcemod; stmts], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
    ExportStmt(syms::Vector{Symbol}, l) =>  to_entities.((m, ), syms, (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
    ModuleStmt(std_imports::Bool, name::Symbol, body::Vector{ToplevelStmts}, l) => 
        to_entities.((m, ), [name; body], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
    ExprStmt(expr::Expression, l) => 
        to_entities(m, expr, make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)))
    ToplevelStmt(exprs::Vector{ToplevelStmts}, l) => 
        to_entities.((m, ), exprs, (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
    MacroExpansionStmt(value::Any, l) => make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent))
end
to_entities(m::TypecheckContext, a::StructField, parent::Union{Entity, Nothing} = nothing) = @match a begin 
    StructField(name::Symbol, type::Union{Expression, Nothing}, attributes::FieldAttributes, l) => 
        to_entities.((m, ), [name; optional_array(type)], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
end

to_entities(m::TypecheckContext, a::Expression, parent::Union{Entity, Nothing} = nothing) = @match a begin
	Literal(expr::Any, l) => make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent))
	Variable(name::Symbol, l) => to_entities(m, name, make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)))
	FunctionDef(name::FunctionName, arguments::Vector{FnArg}, kw_args::Vector{KwArg}, sparams::Vector{TyVar}, rett::Union{Expression, Nothing}, body::Union{Expression, Nothing}, l) =>
        to_entities.((m, ), [name; arguments; kw_args; sparams; optional_array(rett); optional_array(body)], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
	MacroDef(name::ResolvedName, arguments::Vector{FnArg}, sparams::Vector{TyVar}, rett::Union{Expression, Nothing}, body::Union{Expression, Nothing}, l) =>
        to_entities.((m, ), [name; arguments; kw_args; sparams; optional_array(rett); optional_array(body)], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
	Block(exprs::Vector{Expression}, l) =>
        to_entities.((m, ), exprs, (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
	LetBinding(bindings::Vector{Union{Pair{<:LValue, <:Expression}, Symbol}}, body::Expression, l) =>
        to_entities.((m, ), [body], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
	TryCatch(body::Expression, catch_var::Union{Symbol, Nothing}, catch_body::Union{Expression, Nothing}, else_body::Union{Expression, Nothing}, finally_body::Union{Expression, Nothing}, l) =>
        to_entities.((m, ), [body; optional_array(catch_var); optional_array(catch_body); optional_array(else_body); optional_array(finally_body)], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
	CallCurly(receiver::Expression, args::Vector{Union{Expression, TyVar}}, l) =>
        to_entities.((m, ), [receiver; args], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
	Comparison(first::Expression, clauses::Vector{Pair{Expression, Expression}}, l) =>
        to_entities.((m, ), [first; getindex.(clauses, 1); getindex.(clauses, 2)], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
	SemanticAST.Broadcast(op::Expression, l) =>
        to_entities(m, expr, make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)))
	FunCall(receiver::Expression, pos_args::Vector{PositionalArgs}, kw_args::Vector{Union{KeywordArg, SplatArg}}, l) =>
        to_entities.((m, ), [pos_args; pos_args; kw_args], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
	GetIndex(arr::Expression, arguments::Vector{PositionalArgs}, l) =>
        to_entities.((m, ), [arr; arguments], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
	GetProperty(rec::Expression, prop::Union{Symbol, Literal}, l) =>
        to_entities.((m, ), [rec; prop], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
	Assignment(lhs::LValue, rhs::Expression, l) =>
        to_entities.((m, ), [lhs; rhs], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
	Update(op::Symbol, lhs::LValue, rhs::Expression, dotted::Bool, l) =>
        to_entities.((m, ), [op; lhs; rhs], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
	WhereType(type::Expression, vars::Vector{TyVar}, l) =>
        to_entities.((m, ), [type; vars], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
	Declaration(vars::Vector{VarDecl}, l) =>
        to_entities.((m, ), vars, (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
	DoStatement(func::Expression, arguments::Vector{FnArg}, body::Expression, l) =>
        to_entities.((m, ), [func; arguments; body], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
	TupleExpr(exprs::Vector{Union{Expression, Splat}}, l) =>
        to_entities.((m, ), exprs, (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
	NamedTupleExpr(exprs::Vector{NamedTupleBody}, l) =>
        to_entities.((m, ), exprs, (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
	StringInterpolate(components::Vector{Union{String, Expression}}, l) =>
        to_entities.((m, ), filter(x->x isa ASTNode, components), (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
	TypeAssert(val::Expression, typ::Expression, l) =>
        to_entities.((m, ), [val; typ], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
	IfStmt(clauses::Vector{IfClause}, l) =>
        to_entities.((m, ), clauses, (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
	WhileStmt(cond::Expression, body::Expression, l) =>
        to_entities.((m, ), [cond; body], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))  
	BreakStmt(l) => make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent))
	ContinueStmt(l) => make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent))
    ReturnStmt(nothing, l) => make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent))
    ReturnStmt(retval::Expression, l) => to_entities(m, retval, make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)))
	ForStmt(iters::Vector{Pair{LValue, Expression}}, body::Expression, l) =>
        to_entities.((m, ), [getindex.(iters, 1); getindex.(iters, 2); body], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))  
	Vect(elems::Vector{Union{Expression, Splat}}, l) =>
        to_entities.((m, ), elems, (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))  
	HCat(type::Union{Expression, Nothing}, elems::Vector{Union{Expression, Splat}}, l) =>
        to_entities.((m, ), [optional_array(type), optional_array(elems)], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))  
	VCat(type::Union{Expression, Nothing}, rows::Vector{Union{Row, Expression, Splat}}, l) =>
        to_entities.((m, ), [optional_array(type); rows], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))  
	NCat(type::Union{Expression, Nothing}, dim::Int, rows::Vector{Union{NRow, Expression}}, l) =>
        to_entities.((m, ), [optional_array(type); rows], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))  
	Generator(flatten::Bool, expr::Expression, iterators::Vector{Iterspec}, l) =>
        to_entities.((m, ), [expr; iterators], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))  
	Comprehension(type::Union{Expression, Nothing}, gen::Generator, l) =>
        to_entities.((m, ), [optional_array(type); gen], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))  
	Quote(ast::JuliaSyntax.SyntaxNode, l) => make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent))
    MacroExpansion(value::Any, l) => make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent))
    Ternary(cond::Expression, then::Expression, els::Expression, l) =>
        to_entities.((m, ), [cond; then; els], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))  
end

to_entities(m::TypecheckContext, a::CallArg, parent::Union{Entity, Nothing} = nothing) = @match a begin 
        PositionalArg(body::Expression, l) => to_entities(m, body, make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)))
        KeywordArg(name::Symbol, value::Expression, l) => to_entities.((m, ), [name; value], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))  
        SplatArg(body::Union{Expression, Nothing}, l) => to_entities(m, body, make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)))
end

to_entities(m::TypecheckContext, a::ImportPath, parent::Union{Entity, Nothing} = nothing) = @match a begin 
	ImportField(source::ImportPath, name::Symbol, l) => to_entities.((m, ), [source; name], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
	ImportId(name::Symbol, l) => to_entities(m, name, make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)))
	ImportRelative(levels::Int, l) => make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent))
end

to_entities(m::TypecheckContext, a::DepClause, parent::Union{Entity, Nothing} = nothing) = @match a begin 
	Dep(path::ImportPath, l) => to_entities(m, path, make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)))
	AliasDep(path::ImportPath, alias::Symbol, l) => to_entities.((m, ), [path, alias], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
end


to_entities(m::TypecheckContext, a::LValue, parent::Union{Entity, Nothing} = nothing) = @match a begin 
        IdentifierAssignment(id::Symbol, l) => to_entities(m, id, make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)))
        OuterIdentifierAssignment(id::Symbol, l) => to_entities(m, id, make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)))
        FieldAssignment(obj::Expression, name::Symbol, l) => to_entities.((m, ), [obj, name], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
        TupleAssignment(params::Vector{LValue}, l) => to_entities.((m, ), params, (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
        RefAssignment(arr::Expression, arguments::Vector{PositionalArgs}, kwargs::Vector{KeywordArg}, l) =>
                to_entities.((m, ), [arr; arguments; kwargs], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
        VarargAssignment(tgt::Union{Nothing, LValue}, l) =>
                to_entities.((m, ), optional_array(tgt), (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
        TypedAssignment(lhs::LValue, type::Expression, l) =>
                to_entities.((m, ), [lhs, type], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
        NamedTupleAssignment(params::Vector{Union{IdentifierAssignment, TypedAssignment}}, l) =>
                to_entities.((m, ), params, (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
        FunctionAssignment(name::FunctionName, args_stmts::Vector{FnArg}, kwargs_stmts::Vector{KwArg}, sparams::Vector{TyVar}, rett::Union{Expression, Nothing}, l) =>
                to_entities.((m, ), [name; args_stmts; kwargs_stmts; sparams; optional_array(rett)], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
        BroadcastAssignment(lhs::LValue, l) => to_entities(m, lhs, make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)))
        UnionAllAssignment(name::LValue, tyargs::Vector{TyVar}, l) => to_entities.((m, ), [name; tyargs], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
end

to_entities(m::TypecheckContext, a::FunctionName, parent::Union{Entity, Nothing} = nothing) = @match a begin 
	ResolvedName(path::Vector{Symbol}, l) => to_entities.((m, ), path, (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
	DeclName(binding::Union{LValue, Nothing}, typ::Expression, l) => to_entities.((m, ), [optional_array(binding); typ], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
	TypeFuncName(receiver::Expression, args::Vector{Union{Expression, TyVar}}, l) => 
                to_entities.((m, ), [receiver;args], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
	AnonFuncName(l) => make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent))
end

to_entities(m::TypecheckContext, a::FnArg, parent::Union{Entity, Nothing} = nothing) = 
        let l = a.location; 
                to_entities.((m, ), [optional_array(a.binding); optional_array(a.default_value); optional_array(a.type)], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
        end
to_entities(m::TypecheckContext, a::TyVar, parent::Union{Entity, Nothing} = nothing) = 
        let l = a.location; 
                to_entities.((m, ), [optional_array(a.name); optional_array(a.ub); optional_array(a.lb)], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
        end
to_entities(m::TypecheckContext, a::IfClause, parent::Union{Entity, Nothing} = nothing) = 
        let l = a.location; 
                to_entities.((m, ), [optional_array(a.cond); a.body], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
        end
to_entities(m::TypecheckContext, a::KwArg, parent::Union{Entity, Nothing} = nothing) = 
        let l = a.location; 
                to_entities.((m, ), [a.name; optional_array(a.type); optional_array(a.default_value)], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
        end
to_entities(m::TypecheckContext, a::VarDecl, parent::Union{Entity, Nothing} = nothing) = 
        let l = a.location; 
                to_entities.((m, ), [a.binding; optional_array(a.value)], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
        end

to_entities(m::TypecheckContext, a::Rows, parent::Union{Entity, Nothing} = nothing) = @match a begin 
        Splat(body::Expression, l) => to_entities(m, body, make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)))
        Row(elems::Vector{Union{Expression, Splat}}, l) => to_entities.((m, ), elems, (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
        NRow(dim::Int, elems::Vector{Union{NRow, Expression}}, l) => to_entities.((m, ), elems, (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
end
to_entities(m::TypecheckContext, a::Iterspec, parent::Union{Entity, Nothing} = nothing) = @match a begin 
	IterEq(lhs::LValue, rhs::Expression, l) => to_entities.((m, ), [lhs, rhs], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
	Filter(inner::Vector{Iterspec}, cond::Expression, l) => to_entities.((m, ), [inner; cond], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
end
to_entities(m::TypecheckContext, a::NamedTupleBody, parent::Union{Entity, Nothing} = nothing) = @match a begin 
        NamedValue(name::Symbol, value::Expression, l) => to_entities.((m, ), [name; value], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
        ComputedNamedValue(name::Expression, value::Expression, l) => to_entities.((m, ), [name; value], (make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)), ))
        SplattedNamedValue(splat::Expression, l) => to_entities(m, splat, make_node(m, l, a, e -> m.ledger[e] = ASTComponent(a, parent)))
end