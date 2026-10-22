import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0078 : Tree := Tree.gram
def path0078 : List Bool := [false,false,true,false,false,false,true,true,false,true,true,false,false,false,false]
theorem checked0078 : pathOK rootState path0078=true ∧ check axisLookup localCores (atPath rootState path0078) tree0078=true := by decide +kernel
end ThomsonNine.PackedMain
