import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0306 : Tree := Tree.gram
def path0306 : List Bool := [false,false,true,false,false,false,true,true,true,false,false,false,true,true,false,true,true,true,true,true,false,true,true,true,false,false,true,true,false]
theorem checked0306 : pathOK rootState path0306=true ∧ check axisLookup localCores (atPath rootState path0306) tree0306=true := by decide +kernel
end ThomsonNine.PackedMain
