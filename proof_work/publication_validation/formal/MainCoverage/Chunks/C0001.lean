import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0001 : Tree := Tree.gram
def path0001 : List Bool := [false,false,false,false,false,true,false]
theorem checked0001 : pathOK rootState path0001=true ∧ check axisLookup localCores (atPath rootState path0001) tree0001=true := by decide +kernel
end ThomsonNine.PackedMain
