import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0308 : Tree := Tree.gram
def path0308 : List Bool := [false,false,true,false,false,false,true,true,true,false,false,false,true,true,false,true,true,true,true,true,false,true,true,true,false,false,true,true,true,false,true,false]
theorem checked0308 : pathOK rootState path0308=true ∧ check axisLookup localCores (atPath rootState path0308) tree0308=true := by decide +kernel
end ThomsonNine.PackedMain
