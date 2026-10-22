import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0292 : Tree := Tree.gram
def path0292 : List Bool := [false,false,true,false,false,false,true,true,true,false,false,false,true,true,false,true,true,false]
theorem checked0292 : pathOK rootState path0292=true ∧ check axisLookup localCores (atPath rootState path0292) tree0292=true := by decide +kernel
end ThomsonNine.PackedMain
