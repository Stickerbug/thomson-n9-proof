import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0476 : Tree := (Tree.split 1 (Tree.split 1 (Tree.positive 0 13 12 22) (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.split 1 (Tree.positive 0 30 29 50) (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.positive 0 61 60 51)) (Tree.order 0 1)))) (Tree.order 0 1))) (Tree.positive 0 13 13 8))
def path0476 : List Bool := [false,false,true,false,false,true,true,true,false,true]
theorem checked0476 : pathOK rootState path0476=true ∧ check axisLookup localCores (atPath rootState path0476) tree0476=true := by decide +kernel
end ThomsonNine.PackedMain
