import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0423 : Tree := (Tree.split 18 (Tree.split 18 Tree.gram (Tree.positive 1 59 61 90)) (Tree.positive 1 59 62 44))
def path0423 : List Bool := [false,false,true,false,false,false,true,true,true,false,true,false,true,false,false,false]
theorem checked0423 : pathOK rootState path0423=true ∧ check axisLookup localCores (atPath rootState path0423) tree0423=true := by decide +kernel
end ThomsonNine.PackedMain
