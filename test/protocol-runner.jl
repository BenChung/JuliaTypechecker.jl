using Distributed, Pkg

to_analyze = ["DuckDB", "Pluto", "Flux", "IJulia", "DifferentialEquations", "Genie", "JuMP", "MakieCore", "Gadfly", "Turing"]

deps = Dict{String, Vector{String}}()
global_deps = Pkg.dependencies()
for pkg in to_analyze
    for pkginfo in values(global_deps)
        if pkginfo.name == pkg 
            deps[pkg] = collect(keys(pkginfo.dependencies))
        end
    end
end

function analyze(dep, owner)
    if isfile("test/results/$owner/$(dep)_interfaces.csv")
        return
    end
    println("doing $dep in $owner")
    worker = addprocs(1)[1]
    sym_mod = Symbol(dep)
    t = @spawnat worker begin
        include("test/protocol-analysis.jl")
        @eval using $sym_mod
        runner = getfield(Main, :run_analysis)
        Base.invokelatest(runner, owner, sym_mod)
    end
    wait(t)
    rmprocs([worker])
end

for kv in deps
    owner, moddeps = kv
    println("doing $owner")
    for dep in moddeps
        analyze(dep, owner)
    end 
    analyze(owner, owner)
end
