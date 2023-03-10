module JuliaTypechecker
using JuliaSyntax
import JuliaSyntax: SyntaxNode
using SemanticAST, MLStyle, Overseer, SymbolServer
import SemanticAST: ASTNode, ToplevelStmts, SourcePosition

@component struct TypeError end

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
    file_resolver::FileSource
    store::Union{SymbolServerInstance, Nothing}
end

load_file(f::FileSource, relative_root::String, filename::String) = f.files[filename]
has_file(f::FileSource, relative_root::String, filename::String) = haskey(f.files, filename)

struct LiveFileSource <: FileSource end
load_file(::LiveFileSource, relative_root::String, filename::String) = read(joinpath(dirname(relative_root),filename), String)
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