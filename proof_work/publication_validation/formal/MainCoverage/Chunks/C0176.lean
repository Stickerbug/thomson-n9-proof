import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0176 : Tree := (Tree.positive 0 117 118 84)
def path0176 : List Bool := [false,false,true,false,false,false,true,true,false,true,true,false,true,true,true,false,false,true,false,true]
theorem checked0176 : pathOK rootState path0176=true ∧ check axisLookup localCores (atPath rootState path0176) tree0176=true := by decide +kernel
end ThomsonNine.PackedMain
