import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0415 : Tree := (Tree.split 19 (Tree.split 18 (Tree.split 18 (Tree.order 0 1) (Tree.split 18 (Tree.split 16 Tree.gram (Tree.order 0 1)) (Tree.split 2 (Tree.split 2 (Tree.order 0 1) (Tree.split 2 (Tree.positive 1 343 342 553) (Tree.split 2 (Tree.split 2 (Tree.order 0 1) (Tree.split 2 (Tree.positive 1 597 596 963) (Tree.split 2 (Tree.positive 1 1017 596 964) (Tree.order 0 1)))) (Tree.order 0 1)))) (Tree.order 0 1)))) (Tree.order 0 1)) (Tree.split 3 (Tree.split 3 (Tree.order 0 1) (Tree.split 3 (Tree.split 3 (Tree.split 3 (Tree.order 0 1) (Tree.split 3 (Tree.split 3 (Tree.split 3 (Tree.order 0 1) (Tree.split 3 (Tree.split 3 (Tree.split 3 (Tree.order 0 1) (Tree.split 3 (Tree.split 2 (Tree.positive 1 1668 1016 1636) (Tree.order 0 1)) (Tree.positive 0 1017 1016 1637))) (Tree.order 0 1)) (Tree.positive 0 597 596 966))) (Tree.order 0 1)) (Tree.positive 0 343 342 556))) (Tree.order 0 1)) (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.positive 0 343 342 316)) (Tree.order 0 1)))) (Tree.order 0 1)))
def path0415 : List Bool := [false,false,true,false,false,false,true,true,true,false,false,false,true,true,true,true,true,false,true,false]
theorem checked0415 : pathOK rootState path0415=true ∧ check axisLookup localCores (atPath rootState path0415) tree0415=true := by decide +kernel
end ThomsonNine.PackedMain
