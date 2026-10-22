import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0289 : Tree := Tree.gram
def path0289 : List Bool := [false,false,true,false,false,false,true,true,true,false,false,false,true,false]
theorem checked0289 : pathOK rootState path0289=true ∧ check axisLookup localCores (atPath rootState path0289) tree0289=true := by decide +kernel
end ThomsonNine.PackedMain
