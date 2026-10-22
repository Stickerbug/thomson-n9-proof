import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0481 : Tree := (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 1 2) (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 1 2) (Tree.positive 0 2 6 5)) (Tree.order 1 2)) (Tree.split 1 (Tree.split 1 (Tree.order 1 2) (Tree.positive 0 3 6 5)) (Tree.order 1 2)))) (Tree.order 1 2)) (Tree.split 1 (Tree.split 1 (Tree.order 1 2) (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 1 2) (Tree.positive 0 4 6 5)) (Tree.order 1 2)) (Tree.split 1 (Tree.split 1 (Tree.order 1 2) (Tree.positive 0 5 6 5)) (Tree.order 1 2)))) (Tree.order 1 2)))
def path0481 : List Bool := [false,true,false]
theorem checked0481 : pathOK rootState path0481=true ∧ check axisLookup localCores (atPath rootState path0481) tree0481=true := by decide +kernel
end ThomsonNine.PackedMain
