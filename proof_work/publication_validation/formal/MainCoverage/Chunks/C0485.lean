import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0485 : Tree := (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.split 1 (Tree.order 0 2) (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.split 1 (Tree.order 0 2) (Tree.positive 0 6 5 5))) (Tree.order 0 1)))) (Tree.order 0 1)) (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.positive 0 6 5 0)) (Tree.order 0 1)) (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.positive 0 6 5 1)) (Tree.order 0 1)))) (Tree.order 0 1)))
def path0485 : List Bool := [true,false]
theorem checked0485 : pathOK rootState path0485=true ∧ check axisLookup localCores (atPath rootState path0485) tree0485=true := by decide +kernel
end ThomsonNine.PackedMain
