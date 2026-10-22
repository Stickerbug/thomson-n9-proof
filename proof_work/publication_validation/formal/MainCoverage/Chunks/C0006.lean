import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0006 : Tree := Tree.gram
def path0006 : List Bool := [false,false,false,false,false,true,true,true,true,true,true,false]
theorem checked0006 : pathOK rootState path0006=true ∧ check axisLookup localCores (atPath rootState path0006) tree0006=true := by decide +kernel
end ThomsonNine.PackedMain
