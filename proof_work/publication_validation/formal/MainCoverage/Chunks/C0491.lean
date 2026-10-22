import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0491 : Tree := (Tree.positive 0 20 23 22)
def path0491 : List Bool := [true,true,true,false,true,true,true,false,false,false,true,false]
theorem checked0491 : pathOK rootState path0491=true ∧ check axisLookup localCores (atPath rootState path0491) tree0491=true := by decide +kernel
end ThomsonNine.PackedMain
