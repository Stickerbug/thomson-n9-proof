import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0327 : Tree := (Tree.split 2 (Tree.positive 1 1691 1690 2461) (Tree.split 2 (Tree.split 2 (Tree.order 0 1) (Tree.split 2 (Tree.positive 1 2565 2564 2996) (Tree.split 2 (Tree.split 2 (Tree.order 0 1) (Tree.split 2 (Tree.positive 1 3110 3109 3284) (Tree.split 2 (Tree.positive 1 3410 3109 3285) (Tree.order 0 1)))) (Tree.order 0 1)))) (Tree.order 0 1)))
def path0327 : List Bool := [false,false,true,false,false,false,true,true,true,false,false,false,true,true,false,true,true,true,true,true,false,true,true,true,false,false,true,true,true,true,true,true,false,true,false]
theorem checked0327 : pathOK rootState path0327=true ∧ check axisLookup localCores (atPath rootState path0327) tree0327=true := by decide +kernel
end ThomsonNine.PackedMain
