import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0081 : Tree := Tree.gram
def path0081 : List Bool := [false,false,true,false,false,false,true,true,false,true,true,false,false,false,true,true,true,false]
theorem checked0081 : pathOK rootState path0081=true ∧ check axisLookup localCores (atPath rootState path0081) tree0081=true := by decide +kernel
end ThomsonNine.PackedMain
