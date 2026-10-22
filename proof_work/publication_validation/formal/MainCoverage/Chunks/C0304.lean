import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0304 : Tree := Tree.gram
def path0304 : List Bool := [false,false,true,false,false,false,true,true,true,false,false,false,true,true,false,true,true,true,true,true,false,true,true,true,false,false,false]
theorem checked0304 : pathOK rootState path0304=true ∧ check axisLookup localCores (atPath rootState path0304) tree0304=true := by decide +kernel
end ThomsonNine.PackedMain
