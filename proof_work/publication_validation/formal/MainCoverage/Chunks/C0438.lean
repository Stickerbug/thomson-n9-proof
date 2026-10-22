import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0438 : Tree := (Tree.positive 1 60 62 44)
def path0438 : List Bool := [false,false,true,false,false,false,true,true,true,false,true,false,true,false,false,true,true]
theorem checked0438 : pathOK rootState path0438=true ∧ check axisLookup localCores (atPath rootState path0438) tree0438=true := by decide +kernel
end ThomsonNine.PackedMain
