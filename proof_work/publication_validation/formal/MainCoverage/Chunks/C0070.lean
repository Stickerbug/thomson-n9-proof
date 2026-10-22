import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0070 : Tree := (Tree.positive 0 14 15 5)
def path0070 : List Bool := [false,false,false,true,true,true,false,false,true,false,true]
theorem checked0070 : pathOK rootState path0070=true ∧ check axisLookup localCores (atPath rootState path0070) tree0070=true := by decide +kernel
end ThomsonNine.PackedMain
