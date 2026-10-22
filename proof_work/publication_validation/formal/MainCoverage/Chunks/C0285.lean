import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0285 : Tree := (Tree.positive 0 62 64 42)
def path0285 : List Bool := [false,false,true,false,false,false,true,true,false,true,true,true,false,true,false,true,true]
theorem checked0285 : pathOK rootState path0285=true ∧ check axisLookup localCores (atPath rootState path0285) tree0285=true := by decide +kernel
end ThomsonNine.PackedMain
