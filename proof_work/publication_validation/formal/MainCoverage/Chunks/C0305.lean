import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0305 : Tree := Tree.gram
def path0305 : List Bool := [false,false,true,false,false,false,true,true,true,false,false,false,true,true,false,true,true,true,true,true,false,true,true,true,false,false,true,false]
theorem checked0305 : pathOK rootState path0305=true ∧ check axisLookup localCores (atPath rootState path0305) tree0305=true := by decide +kernel
end ThomsonNine.PackedMain
