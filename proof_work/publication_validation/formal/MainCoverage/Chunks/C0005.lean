import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0005 : Tree := Tree.gram
def path0005 : List Bool := [false,false,false,false,false,true,true,true,true,true,false]
theorem checked0005 : pathOK rootState path0005=true ∧ check axisLookup localCores (atPath rootState path0005) tree0005=true := by decide +kernel
end ThomsonNine.PackedMain
