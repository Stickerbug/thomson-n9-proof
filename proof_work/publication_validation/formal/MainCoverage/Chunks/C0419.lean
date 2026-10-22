import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0419 : Tree := (Tree.positive 0 112 112 174)
def path0419 : List Bool := [false,false,true,false,false,false,true,true,true,false,false,false,true,true,true,true,true,false,true,true,true]
theorem checked0419 : pathOK rootState path0419=true ∧ check axisLookup localCores (atPath rootState path0419) tree0419=true := by decide +kernel
end ThomsonNine.PackedMain
