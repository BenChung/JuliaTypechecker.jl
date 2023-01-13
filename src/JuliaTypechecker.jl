module JuliaTypechecker
using JuliaSyntax
import JuliaSyntax: SyntaxNode
using SemanticAST, Overseer, MLStyle
import SemanticAST: ASTNode, ToplevelStmts, SourcePosition

abstract type FileSource end
struct DictFileSource <: FileSource
    files::Dict{String, String}
end
load_file(f::FileSource, relative_root::String, filename::String) = f.files[filename]

struct LiveFileSource <: FileSource end
load_file(::LiveFileSource, relative_root::String, filename::String) = read(joinpath(dirname(relative_root),filename), String)

const Path = Vector{Symbol}
@component struct ScopeInfo 
    path::Path
    root::Entity
    parent::Union{Entity, Nothing}
    children::Vector{Entity}
    definitions::Dict{Symbol, Binding}
    exports::Set{Symbol}
end

abstract type AbstractType 
end

struct FnDef 
    args::Vector{T where T<:AbstractType}
end
struct ModuleInfo 
    sources::Vector{ScopeInfo}
    ftable::Vector{FnDef}
end

mutable struct TypecheckContext 
    ledger::Ledger
    node_mapping::Dict{ASTNode, Entity}
    file_resolver::FileSource
end

abstract type SourceInfo end
include("toplevel.jl")
include("scope-analyzer.jl")
include("binding-analyzer.jl")

function analyze_from_root(file::String)
    r = LiveFileSource()
    stage = Stage(:typechecker, [])
    m = Ledger(stage)
    ctx = TypecheckContext(m, Dict{ASTNode, Entity}(), r)

    entry = expand_toplevel(JuliaSyntax.parseall(JuliaSyntax.SyntaxNode, read(file, String)), ExpandCtx(true, false))
    JuliaTypechecker.to_entities(ctx, entry, nothing)
    root = m[ctx.node_mapping[entry]]
    
    toplevel_scope = ScopeInfo([:Main], root, nothing, [], Dict{Symbol, Binding}(), Set{Symbol}())
    ctx.root_scope = toplevel_scope
    m[ctx.node_mapping[entry]] = toplevel_scope
    m[ctx.node_mapping[entry]] = IncludeFiles(file, [])
    
    analyze_scope(ctx, [:Main], toplevel_scope, entry)
    ctx
end

export FileSource, DictFileSource, LiveFileSource, TypecheckContext
end