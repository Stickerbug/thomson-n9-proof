import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0486 : Tree := (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 0 2) (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 0 2) (Tree.positive 0 6 6 5)) (Tree.order 1 2)) (Tree.order 0 2))) (Tree.order 1 2)) (Tree.order 0 2))
def path0486 : List Bool := [true,true,false]
theorem checked0486 : pathOK rootState path0486=true ∧ check axisLookup localCores (atPath rootState path0486) tree0486=true := by decide +kernel
end ThomsonNine.PackedMain
