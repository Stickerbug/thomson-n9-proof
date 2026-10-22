import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0291 : Tree := Tree.gram
def path0291 : List Bool := [false,false,true,false,false,false,true,true,true,false,false,false,true,true,false,true,false]
theorem checked0291 : pathOK rootState path0291=true ∧ check axisLookup localCores (atPath rootState path0291) tree0291=true := by decide +kernel
end ThomsonNine.PackedMain
