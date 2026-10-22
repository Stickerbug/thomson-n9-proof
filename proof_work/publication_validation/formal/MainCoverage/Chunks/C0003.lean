import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0003 : Tree := Tree.gram
def path0003 : List Bool := [false,false,false,false,false,true,true,true,false]
theorem checked0003 : pathOK rootState path0003=true ∧ check axisLookup localCores (atPath rootState path0003) tree0003=true := by decide +kernel
end ThomsonNine.PackedMain
