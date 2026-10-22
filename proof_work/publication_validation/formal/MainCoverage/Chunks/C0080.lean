import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0080 : Tree := Tree.gram
def path0080 : List Bool := [false,false,true,false,false,false,true,true,false,true,true,false,false,false,true,true,false]
theorem checked0080 : pathOK rootState path0080=true ∧ check axisLookup localCores (atPath rootState path0080) tree0080=true := by decide +kernel
end ThomsonNine.PackedMain
