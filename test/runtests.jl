using JuliaTypechecker, JuliaSyntax, Overseer, SymbolServer
using SemanticAST
import SemanticAST: just_argslist, flatten_where_expr, analyze_typevar, ASTException, ASTNode
import JuliaTypechecker: Binding, Path, PathInfo, analyze_scope, ModuleDefinition, IncludeFiles, TypeError, get_definition, get_definition_descending, analyze_bindings, ScopeInfo, InFile, Definition, ToplevelContext
import JuliaTypechecker: convert_runtime_type, JuliaType, NominalType, TypeVarType, TupleType, UnionType, AnyType, UnionAllType, TypeLitType, TypeVarDef
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
				ssi = SymbolServerInstance(".", nothing)
				ctx = TypecheckContext(m, Dict{ASTNode, Entity}(), r, ssi)
                JuliaTypechecker.to_entities(ctx, expand_toplevel(childof(JuliaSyntax.parseall(SN, input), 1), ExpandCtx(true, false)), nothing)
				@test true
			end
		end
	end
end

has_error(c::TypecheckContext) = TypeError in c.ledger && !isempty(@entities_in(c.ledger[TypeError]))
has_file(ctx::TypecheckContext, filename::String) = any(e->e.path == filename, @entities_in(ctx.ledger, InFile))

scope_tests() = [
	:includes => [
		["root" => "include(\"testme.jl\")", "testme.jl" => "module Foo end"] => (c, s) -> !has_error(c) && has_file(c, "testme.jl"),
		["root" => "include(\"testme.jl\")", "testme.jl" => "include(\"testme2.jl\")", "testme2.jl"=>"module Foo end"] => (c, s) -> !has_error(c) && has_file(c, "testme.jl") && has_file(c, "testme2.jl"),
		["root" => "module Foo include(\"testme.jl\") end", "testme.jl" => "module Bar end"] => (c, s) -> !has_error(c) && has_file(c, "testme.jl"),
		["root" => "module Foo include(\"testme2.jl\") end"] => (c, s) -> has_error(c),
		["root" => "module Foo include(\"testme.jl\") end", "testme.jl" => "module Bar end", "testme2.jl" => "module Baz end"] => (c, s) -> !has_error(c) && has_file(c, "testme.jl") && !has_file(c, "testme2.jl"),
	]
]

@testset "File structure analysis" begin
	@testset "$head" for (head, tests) in scope_tests()
		for (fileset, predicate) in tests 
			filedict = Dict{String, String}(fileset)
			r = DictFileSource(filedict)
			stage = Stage(:typechecker, [])
			m = Ledger(stage)
			ssi = SymbolServerInstance(".", nothing)
			ctx = TypecheckContext(m, Dict{ASTNode, Entity}(), r, ssi)

			entry = expand_toplevel(JuliaSyntax.parseall(JuliaSyntax.SyntaxNode, filedict["root"]), ExpandCtx(true, false))
			JuliaTypechecker.to_entities(ctx, entry, nothing)
			root = m[ctx.node_mapping[entry]]
			
			toplevel_scope = ScopeInfo([:Main], root, nothing, [])
			m[ctx.node_mapping[entry]] = toplevel_scope
			m[ctx.node_mapping[entry]] = JuliaTypechecker.InFile("")
			
			analyze_scope(ctx, [:Main], toplevel_scope, entry)
			@test predicate(ctx, toplevel_scope)
		end
	end
end

has_definition(c::ToplevelContext, n::Symbol) = haskey(c.bindings, n)
has_definition(c::Base.ImmutableDict, n::Symbol) = haskey(c, n)
function has_definition(c::Union{ToplevelContext,Base.ImmutableDict}, ns::Vector{Symbol})
	for n in ns
		if !haskey(c, n)
			return false 
		end
		c = c[n]
	end
	return true
end
binding_tests() = [
	:modules => [
		["root" => "module Test end"] => (c,s) -> @test(has_definition(c, :Test))
		["root" => "module Test module Bar end end"] => (c,s) -> begin @test(has_definition(c, :Test)); @test(has_definition(c, [:Test, :Bar])) end
		["root" => "module Test include(\"testme.jl\") end", "testme.jl"=>"module Bar end"] => (c,s) -> begin @test(has_definition(c, :Test)); @test(has_definition(c, [:Test, :Bar])) end
	],
	:definitions => [
		["root" => "x=2"] => (c,s) -> @test(has_definition(c, [:x]))
	]
]


@testset "Binding analysis" begin
	@testset "$head" for (head, tests) in binding_tests()
		for (fileset, predicate) in tests 
			filedict = Dict{String, String}(fileset)
			r = DictFileSource(filedict)
			stage = Stage(:typechecker, [])
			m = Ledger(stage)
			ssi = SymbolServerInstance(".", nothing)
			ctx = TypecheckContext(m, Dict{ASTNode, Entity}(), r, ssi)

			entry = expand_toplevel(JuliaSyntax.parseall(JuliaSyntax.SyntaxNode, filedict["root"]), ExpandCtx(true, false))
			JuliaTypechecker.to_entities(ctx, entry, nothing)
			root = m[ctx.node_mapping[entry]]
			
			toplevel_scope = ScopeInfo([:Main], root, nothing, [])
			m[ctx.node_mapping[entry]] = toplevel_scope
			m[ctx.node_mapping[entry]] = JuliaTypechecker.InFile("")
			
			analyze_scope(ctx, [:Main], toplevel_scope, entry)
			tctx = ToplevelContext(nothing, Base.ImmutableDict{Symbol, Definition}(), [], [])
			fctx = analyze_bindings(ctx, tctx, entry)
			predicate(fctx, toplevel_scope)
		end
	end
end

@testset "type conversions" begin 
	#=
	@testset "runtime to static" begin 
		@test convert_runtime_type(Any) == AnyType()
		@test convert_runtime_type(Int) == NominalType([:Core, :Int64], [])
		@test convert_runtime_type(Vector{Int}) == NominalType([:Core, :Array], JuliaType[NominalType([:Core, :Int64], JuliaType[]), TypeLitType(JuliaTypechecker.ValueTypeLit(1))])
		@test convert_runtime_type(Union{Int, String}) == UnionType(JuliaType[NominalType([:Core, :Int64], JuliaType[]), NominalType([:Core, :String], JuliaType[])])
		@test convert_runtime_type(Tuple{Int, String}) == TupleType(JuliaType[NominalType([:Core, :Int64], JuliaType[]), NominalType([:Core, :String], JuliaType[])])
		@test convert_runtime_type(Union{}) == UnionType(JuliaType[])
		@test convert_runtime_type(Tuple{T, T} where T) == UnionAllType(TupleType(JuliaType[TypeVarType(:T), TypeVarType(:T)]), [TypeVarDef(UnionType([]), :T, AnyType())])
		@test convert_runtime_type(Union{Int, T} where Int<:T<:Number) == UnionAllType(UnionType([NominalType([:Core, :Int64], JuliaType[]), TypeVarType(:T)]), [TypeVarDef(NominalType([:Core, :Int64], []), :T, NominalType([:Core, :Number], []))])
	end
	=#
	parse_type_expr(text) = expand_forms(JuliaSyntax.child(JuliaSyntax.parseall(JuliaSyntax.SyntaxNode, text), 1), ExpandCtx(true, false))
	@testset "expression to static" begin 
		filedict = Dict{String, String}()
		r = DictFileSource(filedict)
		stage = Stage(:typechecker, [])
		m = Ledger(stage)
		ssi = SymbolServerInstance(".", nothing)
		ctx = TypecheckContext(m, Dict{ASTNode, Entity}(), r, ssi)
		default_context = JuliaTypechecker.LocalContext(ctx, Base.ImmutableDict{Symbol, JuliaTypechecker.JlType}(), nothing)

		@test JuliaTypechecker.convert_type(default_context, parse_type_expr("Any"), Base.ImmutableDict{Symbol, TypeVar}()) == JuliaTypechecker.BasicType(Any)
		@test JuliaTypechecker.convert_type(default_context, parse_type_expr("Int"), Base.ImmutableDict{Symbol, TypeVar}()) == JuliaTypechecker.BasicType(Int)
		@test JuliaTypechecker.convert_type(default_context, parse_type_expr("Vector{Int}"), Base.ImmutableDict{Symbol, TypeVar}()) == JuliaTypechecker.BasicType(Vector{Int})
		@test JuliaTypechecker.convert_type(default_context, parse_type_expr("Tuple{Int, String}"), Base.ImmutableDict{Symbol, TypeVar}()) == JuliaTypechecker.BasicType(Tuple{Int, String})
		@test JuliaTypechecker.convert_type(default_context, parse_type_expr("Union{Int, String}"), Base.ImmutableDict{Symbol, TypeVar}()) == JuliaTypechecker.BasicType(Union{Int, String})
		@test JuliaTypechecker.convert_type(default_context, parse_type_expr("Union{}"), Base.ImmutableDict{Symbol, TypeVar}()) == JuliaTypechecker.BasicType(Union{})
		@test JuliaTypechecker.convert_type(default_context, parse_type_expr("Tuple{T, T} where T"), Base.ImmutableDict{Symbol, TypeVar}()) == JuliaTypechecker.BasicType(Tuple{T, T} where T)
		@test JuliaTypechecker.convert_type(default_context, parse_type_expr("Union{Int, T} where Int<:T<:Number"), Base.ImmutableDict{Symbol, TypeVar}()) == JuliaTypechecker.BasicType(Union{Int, T} where Int<:T<:Number)
	end
	
end

parse_expr(text) = expand_forms(JuliaSyntax.child(JuliaSyntax.parseall(JuliaSyntax.SyntaxNode, text), 1), ExpandCtx(true, false))
@testset "typechecking" begin 
	filedict = Dict{String, String}()
	r = DictFileSource(filedict)
	stage = Stage(:typechecker, [])
	m = Ledger(stage)
	ssi = SymbolServerInstance(".", nothing)
	ctx = TypecheckContext(m, Dict{ASTNode, Entity}(), r, ssi)
	default_context = JuliaTypechecker.LocalContext(ctx, Base.ImmutableDict{Symbol, JuliaTypechecker.JlType}(), nothing)
	@test last(JuliaTypechecker.typecheck_expression(default_context, parse_expr("function f(x) x end"))) == JuliaTypechecker.BasicType(Function)
	@test last(JuliaTypechecker.typecheck_expression(default_context, parse_expr("2 + 2"))) == JuliaTypechecker.BasicType(Int)
	@test last(JuliaTypechecker.typecheck_expression(default_context, parse_expr("begin x = 2 * 2 + 3; y = 8 + x; y end"))) == JuliaTypechecker.BasicType(Int)
	@test last(JuliaTypechecker.typecheck_expression(default_context, parse_expr("begin x = 2 * 2 + 3.0; y = 8 + x; y end"))) == JuliaTypechecker.BasicType(Float64)
	@test last(JuliaTypechecker.typecheck_expression(default_context, parse_expr("begin x = Ref(3); x.x end"))) == JuliaTypechecker.BasicType(Int)
	@test last(JuliaTypechecker.typecheck_expression(default_context, parse_expr("let x = 9; x end"))) == JuliaTypechecker.BasicType(Int)
	@test last(JuliaTypechecker.typecheck_expression(default_context, parse_expr("let x = 9; x += 11 end"))) == JuliaTypechecker.BasicType(Int)
end