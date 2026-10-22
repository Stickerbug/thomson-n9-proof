import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0009 : Tree := Tree.gram
def path0009 : List Bool := [false,false,false,false,false,true,true,true,true,true,true,true,true,true,false]
theorem checked0009 : pathOK rootState path0009=true ∧ check axisLookup localCores (atPath rootState path0009) tree0009=true := by decide +kernel
end ThomsonNine.PackedMain
