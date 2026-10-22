import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0084 : Tree := Tree.gram
def path0084 : List Bool := [false,false,true,false,false,false,true,true,false,true,true,false,false,false,true,true,true,true,true,true,false]
theorem checked0084 : pathOK rootState path0084=true ∧ check axisLookup localCores (atPath rootState path0084) tree0084=true := by decide +kernel
end ThomsonNine.PackedMain
