
tc_worker = Distributed.addprocs(1)[1]

function load_package(package)
    tempname, io = mktemp()
    write(io, "using $(package)")
    close(io)
    @eval Distributed.@spawnat tc_worker (include($tempname))
end