using JuliaTypechecker, JuliaSyntax, Overseer
using SemanticAST
import SemanticAST: just_argslist, flatten_where_expr, analyze_typevar, ASTException, ASTNode
import JuliaTypechecker: Binding, Path, PathInfo, analyze_scope, ModuleDefinition, IncludeFiles, TypeError, get_definition, get_definition_descending, analyze_bindings
using Test
const SN = JuliaSyntax.SyntaxNode
const SH = JuliaSyntax.SyntaxHead
childof = JuliaSyntax.child
kindof(ex) = JuliaSyntax.kind(JuliaSyntax.head(ex))
toplevel_tests() = [ 
	:struct => [
		"struct Foo end" => "StructDefStmt(:Foo, Symbol[], nothing, [], [])",
		"struct Foo <: Bar end" => "StructDefStmt(:Foo, Symbol[], Variable(:Bar), [], [])",
		"struct Foo{X} <: Bar end" => "StructDefStmt(:Foo, [:X], Variable(:Bar), [], [])",
		"struct Foo{X} <: Bar{X} end" => "StructDefStmt(:Foo, [:X], CallCurly(Variable(:Bar), [Variable(:X)]), [], [])",
		"struct Foo{X<:Int} <: Bar{X} end" => "StructDefStmt(:Foo, [:X], CallCurly(Variable(:Bar), [Variable(:X)]), [], [])",
		"struct Foo{X, Y} <: Baz{Y} end" => "StructDefStmt(:Foo, [:X, :Y], CallCurly(Variable(:Baz), [Variable(:Y)]), [], [])",
		"struct Foo x end" => "StructDefStmt(:Foo, Symbol[], nothing, [StructField(:x, nothing, FIELD_NONE)], [])",
		"struct Foo x; y end" => "StructDefStmt(:Foo, Symbol[], nothing, [StructField(:x, nothing, FIELD_NONE), StructField(:y, nothing, FIELD_NONE)], [])",
		"struct Foo x::Int end" => "StructDefStmt(:Foo, Symbol[], nothing, [StructField(:x, Variable(:Int), FIELD_NONE)], [])",
		"struct Foo x::Int; y::String end" => "StructDefStmt(:Foo, Symbol[], nothing, [StructField(:x, Variable(:Int), FIELD_NONE), StructField(:y, Variable(:String), FIELD_NONE)], [])",
		"mutable struct Foo x::Int; const y::String end" => "StructDefStmt(:Foo, Symbol[], nothing, [StructField(:x, Variable(:Int), FIELD_NONE), StructField(:y, Variable(:String), FIELD_CONST)], [])"
    ],
	:abstract => [
		"abstract type Foo end" => "AbstractDefStmt(:Foo, Symbol[], nothing)",
		"abstract type Foo <: Bar end" => "AbstractDefStmt(:Foo, Symbol[], Variable(:Bar))",
		"abstract type Foo{X} <: Bar end" => "AbstractDefStmt(:Foo, [:X], Variable(:Bar))",
		"abstract type Foo{X} <: Bar{X} end" => "AbstractDefStmt(:Foo, [:X], CallCurly(Variable(:Bar), [Variable(:X)]))",
		"abstract type Foo{X<:Int} <: Bar{X} end" => "AbstractDefStmt(:Foo, [:X], CallCurly(Variable(:Bar), [Variable(:X)]))",
		"abstract type Foo{X, Y} <: Baz{Y} end" => "AbstractDefStmt(:Foo, [:X, :Y], CallCurly(Variable(:Baz), [Variable(:Y)]))",
		"abstract type A end" => "AbstractDefStmt(:A, Symbol[], nothing)",
		"abstract type A ; end" => "AbstractDefStmt(:A, Symbol[], nothing)",
		"abstract type A <: B end" => "AbstractDefStmt(:A, Symbol[], Variable(:B))",
		"abstract type A <: B{T,S} end" => "AbstractDefStmt(:A, Symbol[], CallCurly(Variable(:B), [Variable(:T), Variable(:S)]))",
	],
	:primitive => [
		"primitive type A 32 end" => "PrimitiveDefStmt(:A, Symbol[], nothing, Literal(32))",
		"primitive type A 32 ; end" => "PrimitiveDefStmt(:A, Symbol[], nothing, Literal(32))",
		"primitive type A <: B \n 8 \n end" => "PrimitiveDefStmt(:A, Symbol[], Variable(:B), Literal(8))"
	],
	:import => [
		"import Foo" => "ImportStmt([Dep(ImportId(:Foo))])",
		"import Foo: bar" => "SourceImportStmt(ImportId(:Foo), [Dep(ImportId(:bar))])",
		"import Foo.bar: baz" => "SourceImportStmt(ImportField(ImportId(:Foo), :bar), [Dep(ImportId(:baz))])",
		"import Foo.bar" => "ImportStmt([Dep(ImportField(ImportId(:Foo), :bar))])",
		"import Foo: baz, bing" => "SourceImportStmt(ImportId(:Foo), [Dep(ImportId(:baz)), Dep(ImportId(:bing))])",
		"import ..Foo" => "ImportStmt([Dep(ImportField(ImportRelative(2), :Foo))])",
		"import ..Foo, ..Baz" => "ImportStmt([Dep(ImportField(ImportRelative(2), :Foo)), Dep(ImportField(ImportRelative(2), :Baz))])",
		"import ..Foo: Baz" => "SourceImportStmt(ImportField(ImportRelative(2), :Foo), [Dep(ImportId(:Baz))])",
		"import Foo: baz as Bar, b.bar" => "SourceImportStmt(ImportId(:Foo), [AliasDep(ImportId(:baz), :Bar), Dep(ImportField(ImportId(:b), :bar))])",
		"import Foo as Bar" => "ImportStmt([AliasDep(ImportId(:Foo), :Bar)])",
		"import Foo as Bar, Bar as Baz" => "ImportStmt([AliasDep(ImportId(:Foo), :Bar), AliasDep(ImportId(:Bar), :Baz)])",
        "import Foo.@baz" => "ImportStmt([Dep(ImportField(ImportId(:Foo), Symbol(\"@baz\")))])",
        "import Foo: @baz" => "SourceImportStmt(ImportId(:Foo), [Dep(ImportId(Symbol(\"@baz\")))])",
        "import Foo.Bar: @baz" => "SourceImportStmt(ImportField(ImportId(:Foo), :Bar), [Dep(ImportId(Symbol(\"@baz\")))])",
	],
	:using => [
		"using Foo" => "UsingStmt([ImportId(:Foo)])",
		"using Foo, Bar" => "UsingStmt([ImportId(:Foo), ImportId(:Bar)])",
		"using Foo, ..Bar" => "UsingStmt([ImportId(:Foo), ImportField(ImportRelative(2), :Bar)])",
		"using Foo: bar" => "SourceUsingStmt(ImportId(:Foo), [Dep(ImportId(:bar))])",
		"using Foo.bar: baz" => "SourceUsingStmt(ImportField(ImportId(:Foo), :bar), [Dep(ImportId(:baz))])",
		"using Foo.bar" => "UsingStmt([ImportField(ImportId(:Foo), :bar)])",
		"using Foo: baz, bing" => "SourceUsingStmt(ImportId(:Foo), [Dep(ImportId(:baz)), Dep(ImportId(:bing))])",
		"using ..Foo" => "UsingStmt([ImportField(ImportRelative(2), :Foo)])",
		"using Foo: baz as Bar, b.bar" => "SourceUsingStmt(ImportId(:Foo), [AliasDep(ImportId(:baz), :Bar), Dep(ImportField(ImportId(:b), :bar))])",
		"using ..Foo, ..Bar" => "UsingStmt([ImportField(ImportRelative(2), :Foo), ImportField(ImportRelative(2), :Bar)])"
	],
	:export => [
		"export foo" => "ExportStmt([:foo])",
		"export foo, bar, baz" => "ExportStmt([:foo, :bar, :baz])"
	],
	:module => [
		"module Foo end" => "ModuleStmt(true, :Foo, [])",
		"module Foo module Bar end end" => "ModuleStmt(true, :Foo, [ModuleStmt(true, :Bar, [])])",
        "baremodule Foo end" => "ModuleStmt(false, :Foo, [])"
	]
]

struct ErrorResult end
@testset "Toplevel to entity" begin
	@testset "$head" for (head, test_specs) in toplevel_tests()
		@testset "$input" for (input, output) in test_specs
			if output isa ErrorResult
				@test_throws ASTException expand_toplevel(JuliaSyntax.parseall(SN, input), ExpandCtx(true, false))
			else 
                stage = Stage(:typechecker, [])
                m = Ledger(stage)
				r = DictFileSource(Dict{String, String}())
				ctx = TypecheckContext(m, Dict{ASTNode, Entity}(), r)
                JuliaTypechecker.to_entities(ctx, expand_toplevel(childof(JuliaSyntax.parseall(SN, input), 1), ExpandCtx(true, false)), nothing)
				@test true
			end
		end
	end
end

has_module(c::TypecheckContext, s::PathInfo, p::Path) = 
	if length(p) > 0
		bnd = get_definition(c, s, first(p))
		if !isnothing(bnd) && bnd.source isa ModuleDefinition 
			has_module(c, bnd.source.local_scope, p[2:end])
		else 
			false
		end
	else
		true
	end

has_error(c::TypecheckContext) = !isempty(@entities_in(c.ledger[TypeError]))

has_binding(c::TypecheckContext, s::PathInfo, b::Symbol) = get_definition(c, s, b) != nothing

scope_tests() = [
	:modules => [
		["root" => "module Foo end"] => (c, s) -> has_module(c, s, [:Foo]),
		["root" => "module Foo end; module Bar end"] => (c, s) -> has_module(c, s, [:Foo]) && has_module(c, s, [:Bar]),
		["root" => "module Foo module Bar end end"] => (c, s) -> has_module(c, s, [:Foo]) && has_module(c, s, [:Foo, :Bar]),
		["root" => "module Foo module Bar end; module Baz end end"] => (c, s) -> has_module(c, s, [:Foo]) && has_module(c, s, [:Foo, :Bar]) && has_module(c, s, [:Foo, :Baz])
	],
	:includes => [
		["root" => "include(\"testme.jl\")", "testme.jl" => "module Foo end"] => (c, s) -> has_module(c, s, [:Foo])
		["root" => "include(\"testme.jl\")", "testme.jl" => "include(\"testme2.jl\")", "testme2.jl"=>"module Foo end"] => (c, s) -> has_module(c, s, [:Foo])
		["root" => "module Foo include(\"testme.jl\") end", "testme.jl" => "module Bar end"] => (c, s) -> has_module(c, s, [:Foo, :Bar])
	]
]
@testset "Scope analysis" begin 
	@testset "$head" for (head, tests) in scope_tests() 
		for (fileset, predicate) in tests 
			filedict = Dict{String, String}(fileset)
			r = DictFileSource(filedict)
			stage = Stage(:typechecker, [])
			m = Ledger(stage)
			ctx = TypecheckContext(m, Dict{ASTNode, Entity}(), r)

			entry = expand_toplevel(JuliaSyntax.parseall(JuliaSyntax.SyntaxNode, filedict["root"]), ExpandCtx(true, false))
			JuliaTypechecker.to_entities(ctx, entry, nothing)
			root = m[ctx.node_mapping[entry]]
			
			toplevel_scope = PathInfo([:Main], root, nothing, [], Dict{Symbol, Binding}(), Set{Symbol}())
			m[ctx.node_mapping[entry]] = toplevel_scope
			m[ctx.node_mapping[entry]] = IncludeFiles("", [])
			
			analyze_scope(ctx, [:Main], toplevel_scope, entry)
			@test predicate(ctx, toplevel_scope)
		end
	end
end

binding_tests() = [
	:usings => [
		["root" => "using Test"] => (c, s) -> true,
		["root" => "using Test, Example"] => (c, s) -> true,
		["root" => "using Main: Test as Testme"] => (c, s) -> true,
		["root" => "using Test.Bar"] => (c, s) -> true,
		["root" => "using Test.Bar: baz"] => (c, s) -> true,
		["root" => "using ..Bar: bing as Bing"] => (c, s) -> has_error(c)
	],
	:imports => [
		["root" => "import Foo"] => (c, s) -> has_binding(c, s, :Foo),
		["root" => "import Foo.bar"] => (c, s) -> has_binding(c, s, :bar),
		["root" => "import Foo: bar, baz"] => (c, s) -> has_binding(c, s, :bar) && has_binding(c, s, :baz),
		["root" => "import .Foo: bar"] => (c, s) -> has_binding(c, s, :bar),
		["root" => "import Foo.bar as bing, Foo.baz"] => (c, s) -> has_binding(c, s, :bing) && has_binding(c, s, :baz)
	],
	:exports => [
		["root" => "export baz, bing"] => (c, s) -> true
	],
	:simple_defns => [
		["root" => "x = 3"] => (c, s) -> has_binding(c, s, :x),
		["root" => "x::Int = 3"] => (c, s) -> has_binding(c, s, :x),
		["root" => "x = 3; y = 9"] => (c, s) -> has_binding(c, s, :x) && has_binding(c, s, :y),
		["root" => "x = []"] => (c, s) -> has_binding(c, s, :x),
		["root" => "(x, y) = []"] => (c, s) -> has_binding(c, s, :x) && has_binding(c, s, :y),
		["root" => "(;x, y) = (x=2, y=3)"] => (c, s) -> has_binding(c, s, :x) && has_binding(c, s, :y),
		["root" => "x{y} = Vector{y}"] => (c, s) -> has_binding(c, s, :x)
		
	]
]
@testset "Binding analysis" begin 
	@testset "$head" for (head, tests) in binding_tests() 
		for (fileset, predicate) in tests 
			filedict = Dict{String, String}(fileset)
			r = DictFileSource(filedict)
			stage = Stage(:typechecker, [])
			m = Ledger(stage)
			ctx = TypecheckContext(m, Dict{ASTNode, Entity}(), r)

			entry = expand_toplevel(JuliaSyntax.parseall(JuliaSyntax.SyntaxNode, filedict["root"]), ExpandCtx(true, false))
			JuliaTypechecker.to_entities(ctx, entry, nothing)
			root = m[ctx.node_mapping[entry]]
			
			toplevel_scope = PathInfo([:Main], root, nothing, [], Dict{Symbol, Binding}(), Set{Symbol}())
			m[ctx.node_mapping[entry]] = toplevel_scope
			m[ctx.node_mapping[entry]] = IncludeFiles("", [])
			
			analyze_scope(ctx, [:Main], toplevel_scope, entry)
			analyze_bindings(ctx, toplevel_scope, entry)
			@test predicate(ctx, toplevel_scope)
		end
	end
end