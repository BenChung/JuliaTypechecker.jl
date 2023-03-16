using CSV
using Plots, StatsPlots
using DataFrames

n_ifaces = DataFrame("Package" => [], "Protocols"=>[])
summary = DataFrame(:package => [], :strict_interfaces=>[], :partial_interfaces=>[], :specialized=>[])
last = nothing
for dir in readdir("test/results")
    interfaces_df = DataFrame([:mod=>[], :abstype=>[], :type =>[], :mname =>[], :argindex =>[], :nargs =>[], :mth =>[]])
    summary_df = DataFrame([:type=>[], :strict_interfaces=>[], :partial_interfaces=>[], :specialized=>[]])

    for file in readdir(joinpath("test/results", dir))
        if occursin(r".*\_interfaces.csv", file)
            append!(interfaces_df, CSV.read(joinpath("test/results",dir,file), DataFrame))
        end
        if occursin(r".*\_summary.csv", file)
            append!(summary_df, CSV.read(joinpath("test/results",dir,file), DataFrame))
        end
    end
    num = length(keys(groupby(interfaces_df, [:abstype, :mname, :argindex, :nargs])))
    pkg_summary = combine(summary_df, :strict_interfaces=>sum=>:strict_interfaces, :partial_interfaces=>sum=>:partial_interfaces, :specialized=>sum=>:specialized)
    
    if dir == "DifferentialEquations"
        dir = "DiffEq"
    end
    insertcols!(pkg_summary, 1, :package => dir)
    push!(n_ifaces, (Package=dir, Protocols=num))
    append!(summary, pkg_summary)
end

@df sort(n_ifaces, :Protocols, rev=true) bar(:Package, :Protocols, xrotation=45, palette=:greys, legend=false)

stackable_summary = sort(select(summary, :package, :strict_interfaces, [:strict_interfaces, :partial_interfaces]=> ((strict, partial)-> partial .- strict) => :only_partial, [:partial_interfaces, :specialized]=> ((strict, partial)-> partial .- strict) => :only_specialized), :strict_interfaces, rev=true)
plt = @df stackable_summary groupedbar(Float64[:only_specialized :only_partial :strict_interfaces], bar_position=:stack, xticks=(1:length(:package),:package), label=["Type-specialized" "Partial protocol" "Complete protocol"], fillcolor=["grey100" "grey50" "grey1"])
Plots.pdf(plt, "test/results/summary.pdf")