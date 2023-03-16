using JuliaTypechecker, JuliaSyntax, Overseer, SymbolServer
using MLStyle
using SemanticAST
import SemanticAST: just_argslist, flatten_where_expr, analyze_typevar, ASTException, ASTNode
import JuliaTypechecker: Binding, Path, PathInfo, analyze_scope, ModuleDefinition, IncludeFiles, TypeError, get_definition, get_definition_descending, analyze_bindings, ScopeInfo, InFile, Definition, ToplevelContext
import JuliaTypechecker: convert_runtime_type, JuliaType, NominalType, TypeVarType, TupleType, UnionType, AnyType, UnionAllType, TypeLitType, TypeVarDef
using Test
const SN = JuliaSyntax.SyntaxNode
const SH = JuliaSyntax.SyntaxHead
childof = JuliaSyntax.child
kindof(ex) = JuliaSyntax.kind(JuliaSyntax.head(ex))
#=
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
				expr = expand_toplevel(childof(JuliaSyntax.parseall(SN, input), 1), ExpandCtx(true, false))
                JuliaTypechecker.to_entities(ctx, expr, nothing)
				SemanticAST.visit(c -> (if c isa ASTNode @test haskey(ctx.node_mapping, c) end), c -> (), expr)
				@test true
			end
		end
	end
end

@testset "Weird nondetermistic thing with if statements" begin 
	for i=1:100
		stage = Stage(:typechecker, [])
		m = Ledger(stage)
		r = DictFileSource(Dict{String, String}())
		ssi = SymbolServerInstance(".", nothing)
		ctx = TypecheckContext(m, Dict{ASTNode, Entity}(), r, ssi)
		expr = expand_toplevel(childof(JuliaSyntax.parseall(SN, "if x < y; end; if x < y; end; if x < y; end; if x < y; end;if x < y; end; if x < y; end"), 1), ExpandCtx(true, false))
		JuliaTypechecker.to_entities(ctx, expr, nothing)
		SemanticAST.visit(c -> (if c isa ASTNode 
			if !haskey(ctx.node_mapping, c)
				println("missing $c")
			end
			@test haskey(ctx.node_mapping, c) 
		end), c -> (), expr)
		@test true
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

		root = Entity(m)
		default_context = JuliaTypechecker.LocalContext(ctx, Base.ImmutableDict{Symbol, JuliaTypechecker.JlType}(), nothing, JuliaTypechecker.ScopeInfo([:Base], root, nothing, Entity[]))

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

@testset "typechecking" begin 

permutecols = """
function permutecols!!(a::AbstractMatrix, p::AbstractVector{<:Integer})
    require_one_based_indexing(a, p)
    count = 0
    start = 0
    while count < (length(p)::Int)
        ptr = start = findnext(!iszero, p, start+1)::Int
        next = p[start]::Int
        count += 1
        while next != start
            swapcols!(a, ptr, next)
            p[ptr] = 0
            ptr = next
            next = p[next]
            count += 1
        end
        p[ptr] = 0
    end
    a
end
"""

evalpoly = """
function _evalpoly(x::Int, p::Vector{Int})
    Base.require_one_based_indexing(p)
    N = length(p)
    ex = p[end]
    for i in N-1:-1:1
        ex = muladd(x, ex, p[i])
    end
    ex
end
"""

evalpoly_complex = """
function _evalpoly(z::Complex, p::Vector{Complex})::Complex
    Base.require_one_based_indexing(p)
    length(p)::Int == 1 && return p[1]
    N = length(p)
    a = p[end]
    b = p[end-1]

    x = real(z)
    y = imag(z)
    r = 2x
    s = muladd(x, x, y*y)
    for i in N-2:-1:1
        ai = a
        a = muladd(r, ai, b)
        b = muladd(-s, ai, p[i])
    end
    ai = a
    muladd(ai, z, b)
end
"""

hypot = """function _hypot(x::Float64, y::Float64)::Float64
# preserves unit
axu = abs(x)
ayu = abs(y)

# unitless
ax = axu / oneunit(axu)
ay = ayu / oneunit(ayu)

# Return Inf if either or both inputs is Inf (Compliance with IEEE754)
if isinf(ax) || isinf(ay)
	return typeof(axu)(Inf)
end

# Order the operands
if ay > ax
	axu, ayu = ayu, axu
	ax, ay = ay, ax
end

# Widely varying operands
if ay <= ax*sqrt(eps(typeof(ax))/2)  #Note: This also gets ay == 0
	return axu
end

# Operands do not vary widely
scale = eps(typeof(ax))*sqrt(floatmin(ax))  #Rescaling constant
if ax > sqrt(floatmax(ax)/2)
	ax = ax*scale
	ay = ay*scale
	scale = inv(scale)
elseif ay < sqrt(floatmin(ax))
	ax = ax/scale
	ay = ay/scale
else
	scale = oneunit(scale)
end
h = sqrt(muladd(ax, ax, ay*ay))
# This branch is correctly rounded but requires a native hardware fma.
if Core.Intrinsics.have_fma(typeof(h))
	hsquared = h*h
	axsquared = ax*ax
	h -= (fma(-ay, ay, hsquared-axsquared) + fma(h, h,-hsquared) - fma(ax, ax, -axsquared))/(2*h)
# This branch is within one ulp of correctly rounded.
else
	if h <= 2*ay
		delta = h-ay
		h -= muladd(delta, delta-2*(ax-ay), ax*(2*delta - ax))/(2*h)
	else
		delta = h-ax
		h -= muladd(delta, delta, muladd(ay, (4*delta - ay), 2*delta*(ax - 2*ay)))/(2*h)
	end
end
return h*scale*oneunit(axu)
end
"""

ldexp = """function ldexp(x::Float64, e::Int)
T = Float64
xu = reinterpret(Unsigned, x)
xs = xu & ~sign_mask(T)
xs >= exponent_mask(T) && return x # NaN or Inf
k = (xs >> significand_bits(T)) % Int
if k == 0 # x is subnormal
	xs == 0 && return x # +-0
	m = leading_zeros(xs) - exponent_bits(T)
	ys = xs << unsigned(m)
	xu = ys | (xu & sign_mask(T))
	k = 1 - m
	# underflow, otherwise may have integer underflow in the following n + k
	(e < -50000)::Bool && return flipsign(T(0.0), x)
end
# For cases where e of an Integer larger than Int make sure we properly
# overflow/underflow; this is optimized away otherwise.
if e > typemax(Int)
	return flipsign(T(Inf), x)
elseif e < typemin(Int)
	return flipsign(T(0.0), x)
end
n = e % Int
k += n
# overflow, if k is larger than maximum possible exponent
if k >= exponent_raw_max(T)
	return flipsign(T(Inf), x)
end
if k > 0 # normal case
	xu = (xu & ~exponent_mask(T)) | (rem(k, uinttype(T)) << significand_bits(T))
	return reinterpret(T, xu)
else # subnormal case
	if k <= -significand_bits(T) # underflow
		# overflow, for the case of integer overflow in n + k
		e > 50000 && return flipsign(T(Inf), x)
		return flipsign(T(0.0), x)
	end
	k += significand_bits(T)
	# z = T(2.0) ^ (-significand_bits(T))
	z = reinterpret(T, rem(exponent_bias(T)-significand_bits(T), uinttype(T)) << significand_bits(T))
	xu = (xu & ~exponent_mask(T)) | (rem(k, uinttype(T)) << significand_bits(T))
	return z*reinterpret(T, xu)
end
end
"""

exponent = """
function exponent(x::Float64)
	T=Float64
    @noinline throw1(x::Float64)::Union{} = throw(DomainError(x, "Cannot be NaN or Inf."))
    @noinline throw2(x::Float64)::Union{} = throw(DomainError(x, "Cannot be ±0.0."))
    xs = reinterpret(Unsigned, x) & ~sign_mask(T)
    xs >= exponent_mask(T) && throw1(x)
    k = Int(xs >> significand_bits(T))
    if k == 0 # x is subnormal
        xs == 0 && throw2(x)
        m = leading_zeros(xs) - exponent_bits(T)
        k = 1 - m
    end
    return k - exponent_bias(T)
end
"""

rad2deg = """rad2deg(z::AbstractFloat)::Any = z * (180 / oftype(z, pi))"""


Base.eval(quote 
	abstract type MyAbstractArray end
	struct MyList <: MyAbstractArray
		array::Array{Int, 1}
	end
	struct MyRange <: MyAbstractArray
		start::Int
		fin::Int
	end
	mylength(v::MyList) = length(v.array)
	mysize(u::MyRange) = u.fin - u.start
	fn(;x=9) = x
end)

	parse_expr(text) = expand_forms(JuliaSyntax.child(JuliaSyntax.parseall(JuliaSyntax.SyntaxNode, text), 1), ExpandCtx(true, false))
	function check_string(str)
		filedict = Dict{String, String}()
		r = DictFileSource(filedict)
		stage = Stage(:typechecker, [])
		m = Ledger(stage)
		ssi = SymbolServerInstance(".", nothing)
		ctx = TypecheckContext(m, Dict{ASTNode, Entity}(), r, ssi)

		
		root = Entity(m)
		default_context = JuliaTypechecker.LocalContext(ctx, Base.ImmutableDict{Symbol, JuliaTypechecker.JlType}(), nothing, JuliaTypechecker.ScopeInfo([:Base], root, nothing, Entity[]))
		expr = parse_expr(str)
		JuliaTypechecker.to_entities(ctx, expr, nothing)
		root = m[ctx.node_mapping[expr]]
		toplevel_scope = ScopeInfo([:Base], root, nothing, [])
		m[ctx.node_mapping[expr]] = toplevel_scope
		m[ctx.node_mapping[expr]] = JuliaTypechecker.InFile("examples/math.jl")

		res = last(JuliaTypechecker.typecheck_expression(default_context, expr)) 
		cs = components(m, JuliaTypechecker.TypeError)
		if length(cs) > 0
			print("Found errors:")
			for e in @entities_in(first(cs))
				println(e)
			end
			for c in first(cs)
				println(stdout, c.msg)
				println()
			end
		end
		return res
	end
	@test check_string("function f(x) x end") == JuliaTypechecker.BasicType(Function)
	@test check_string("2 + 2") == JuliaTypechecker.BasicType(Int)
	@test check_string("begin x = 2 * 2 + 3; y = 8 + x; y end") == JuliaTypechecker.BasicType(Int)
	@test check_string("begin x = 2 * 2 + 3.0; y = 8 + x; y end") == JuliaTypechecker.BasicType(Float64)
	@test check_string("begin x = Ref(3); x.x end") == JuliaTypechecker.BasicType(Int)
	@test check_string("let x = 9; x end") == JuliaTypechecker.BasicType(Int)
	@test check_string("let x = 9; x += 11 end") == JuliaTypechecker.BasicType(Int)
	@test check_string("test(x::Int, y::Int) = x + y") == JuliaTypechecker.BasicType(Function)
	@test check_string("const x = 3") == JuliaTypechecker.BasicType(Int)
	@test check_string("(3, \"hello\", 3.0)") == JuliaTypechecker.BasicType(Tuple{Int, String, Float64})
	@test check_string("for x in [1,2,3] x end") == JuliaTypechecker.BasicType(Nothing)
	@test check_string("let x::Real = 9; x end") == JuliaTypechecker.BasicType(Real)
	@test check_string("factorial(n::Int128) = factorial_lookup(n, _fact_table128, 33)") == JuliaTypechecker.BasicType(Function)
	@test check_string(permutecols) == JuliaTypechecker.BasicType(Function)
	@test check_string(evalpoly) == JuliaTypechecker.BasicType(Function)
	@test check_string(evalpoly_complex) == JuliaTypechecker.BasicType(Function)
	@test check_string(hypot) == JuliaTypechecker.BasicType(Function)
	@test check_string(rad2deg) == JuliaTypechecker.BasicType(Function)
	@test check_string(ldexp) == JuliaTypechecker.BasicType(Function)
	@test check_string("array_like(a::MyAbstractArray) = mylength(a)") == JuliaTypechecker.BasicType(Function)
	@test check_string("fn(;x=3)") == JuliaTypechecker.BasicType(Int64)
	@test check_string("1 < 2 < 3") == JuliaTypechecker.BasicType(Bool)
	@test check_string("begin foo = (bar = 3.0)/2.0; bar end") == JuliaTypechecker.BasicType(Float64)
	#@test check_string(exponent) == JuliaTypechecker.BasicType(Function)
end
=#
function walk_to_function(ctx::TypecheckContext, e)
	currrent_component = ctx.ledger[JuliaTypechecker.ASTComponent][e]
	node = currrent_component.node
	return @match node begin 
		FunctionDef(name, arguments, kwargs, sparams, rett, body, _) => node
		Assignment(FunctionAssignment(name, arguments, kwargs, sparams, rett, _), body, _) => node
		_ => isnothing(currrent_component.parent) ? nothing : walk_to_function(ctx, currrent_component.parent)
	end
end
function extract_errors(ctx::TypecheckContext, expr::SemanticAST.ToplevelStmts) 
	function_errors = Dict{SemanticAST.ASTNode, Vector{JuliaTypechecker.TypeError}}()
	if !(JuliaTypechecker.TypeError in ctx.ledger)
		return function_errors
	end
	for error_entity in @entities_in(ctx.ledger, JuliaTypechecker.TypeError)
		function_node = walk_to_function(ctx, error_entity)
		if isnothing(function_node) continue end
		errors = get!(() -> JuliaTypechecker.TypeError[], function_errors, function_node)
		push!(errors, ctx.ledger[JuliaTypechecker.TypeError][error_entity])
	end
	return function_errors
end

function get_toplevel_functions(expr::SemanticAST.ToplevelStmts, funcs=[])
	@match expr begin
		ToplevelStmt(exprs, _) => get_toplevel_functions.(exprs, (funcs, ))
		ModuleStmt(std_imports, name, body, _) && m => get_toplevel_functions.(body, (funcs, ))
		ExprStmt(FunctionDef(name, arguments, kwargs, sparams, rett, body, _) && fn, _) => push!(funcs, fn)
		ExprStmt(Assignment(FunctionAssignment(name::FunctionName, args_stmts::Vector{FnArg}, kwargs_stmts::Vector{KwArg}, sparams::Vector{TyVar}, rett::Union{Expression, Nothing}, _), body::Expression, _) && assgn, _) => push!(funcs, assgn)
		_ => ()
	end
	return funcs
end
	

@testset "Load mathematics" begin 
	r = LiveFileSource()
	stage = Stage(:typechecker, [])
	m = Ledger(stage)
	ssi = SymbolServerInstance(".", nothing)
	ctx = TypecheckContext(m, Dict{ASTNode, Entity}(), r, ssi)

	entry = expand_toplevel(JuliaSyntax.parseall(JuliaSyntax.SyntaxNode, read("examples/math.jl", String)), ExpandCtx(true, false))
	JuliaTypechecker.to_entities(ctx, entry, nothing)

	root = m[ctx.node_mapping[entry]]
	
	toplevel_scope = ScopeInfo([:Base], root, nothing, [])
	m[ctx.node_mapping[entry]] = toplevel_scope
	m[ctx.node_mapping[entry]] = JuliaTypechecker.InFile("examples/math.jl")
	
	analyze_scope(ctx, [:Base], toplevel_scope, entry)
	funcs = []
	for file_root_entity in @entities_in(m[JuliaTypechecker.InFile])
		root_node = m[JuliaTypechecker.ASTComponent][file_root_entity].node
		JuliaTypechecker.typecheck(ctx, root_node)
		get_toplevel_functions(entry, funcs)
	end
	throw(length(funcs))
	JuliaTypechecker.typecheck(ctx, entry)

	cs = components(m, JuliaTypechecker.TypeError)
	if length((cs)) > 0
		println("Found errors: $(length(first(cs)))")
	end
	fn_errors = extract_errors(ctx, entry)
	
	tlfs = Set(funcs)
	
	for fnerr in fn_errors 
		fn, errs = fnerr 
		delete!(tlfs, fn)
		println("Errors found in function: ")
		show(stdout, fn)
		n =0
		println("")
		for err in errs 
			println("err $n")
			println(err.msg)
			println("")
			n+=1
		end
	end
	println("functions without errors:")
	for tlf in tlfs 
		println(tlf)
	end

	@test false
end