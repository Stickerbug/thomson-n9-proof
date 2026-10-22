import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0309 : Tree := Tree.gram
def path0309 : List Bool := [false,false,true,false,false,false,true,true,true,false,false,false,true,true,false,true,true,true,true,true,false,true,true,true,false,false,true,true,true,false,true,true,false]
theorem checked0309 : pathOK rootState path0309=true ∧ check axisLookup localCores (atPath rootState path0309) tree0309=true := by decide +kernel
end ThomsonNine.PackedMain
