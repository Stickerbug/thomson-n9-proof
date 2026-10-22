import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0361 : Tree := (Tree.split 3 (Tree.split 3 (Tree.split 3 (Tree.split 3 (Tree.order 0 1) (Tree.split 3 (Tree.split 2 (Tree.split 2 (Tree.order 0 1) (Tree.split 2 (Tree.split 2 (Tree.split 2 (Tree.order 0 1) (Tree.split 2 (Tree.split 2 (Tree.split 2 (Tree.order 0 1) (Tree.positive 1 3130 3129 2970)) (Tree.order 0 1)) (Tree.positive 1 2575 2574 2971))) (Tree.order 0 1)) (Tree.positive 1 1696 1695 2450))) (Tree.order 0 1)) (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.positive 0 1696 1695 1597)) (Tree.order 0 1)))) (Tree.order 0 1)) (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.positive 0 1031 1030 946)) (Tree.order 0 1))) (Tree.positive 0 604 604 545))
def path0361 : List Bool := [false,false,true,false,false,false,true,true,true,false,false,false,true,true,false,true,true,true,true,true,false,true,true,true,true,true,false,true]
theorem checked0361 : pathOK rootState path0361=true ∧ check axisLookup localCores (atPath rootState path0361) tree0361=true := by decide +kernel
end ThomsonNine.PackedMain
