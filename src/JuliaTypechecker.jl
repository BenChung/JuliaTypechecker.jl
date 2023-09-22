module JuliaTypechecker
using JuliaSyntax
import JuliaSyntax: SyntaxNode
using SemanticAST, MLStyle, Overseer, SymbolServer
import SemanticAST: ASTNode, ToplevelStmts, SourcePosition

@component struct TypeError
    msg::String
end

abstract type FileSource end
struct DictFileSource <: FileSource
    files::Dict{String, String}
end

const Path = Vector{Symbol}
@component struct ScopeInfo
    path::Path
    root::Entity
    parent::Union{Entity, Nothing}
    children::Vector{Entity}
end

mutable struct TypecheckContext
    ledger::Ledger
    node_mapping::Dict{ASTNode, Entity}
    ast_mapping::Dict{Entity, ASTNode}
    node_parents::Dict{ASTNode, ASTNode}
    file_resolver::FileSource
    store::Union{SymbolServerInstance, Nothing}
    TypecheckContext(ledger::Ledger, file_resolver::FileSource, store::Union{SymbolServerInstance, Nothing}) =
        new(ledger, Dict{ASTNode, Entity}(), Dict{Entity, ASTNode}(), Dict{ASTNode, ASTNode}(), file_resolver, store)

end

load_file(f::FileSource, relative_root::String, filename::String) = f.files[filename]
has_file(f::FileSource, relative_root::String, filename::String) = haskey(f.files, filename)

struct LiveFileSource <: FileSource end
function load_file(::LiveFileSource, relative_root::String, filename::String) 
    println("loading $filename")
    return read(joinpath(dirname(relative_root),filename), String)
end
has_file(::LiveFileSource, relative_root::String, filename::String) = isfile(joinpath(dirname(relative_root),filename))

include("toplevel.jl")
include("scope-analyzer.jl")
include("binding-analyzer.jl")
include("type-analyzer.jl")


function analyze_from_root(file::String)
    r = LiveFileSource()
    ctx
end

export FileSource, DictFileSource, LiveFileSource, TypecheckContext
end