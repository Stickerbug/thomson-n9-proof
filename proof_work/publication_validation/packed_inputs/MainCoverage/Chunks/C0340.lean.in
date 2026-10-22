import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0340 : Tree := (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.positive 0 3414 3413 3282)) (Tree.order 0 1)) (Tree.positive 0 3112 3111 3283))) (Tree.order 0 1)) (Tree.positive 0 2566 2565 2997)) (Tree.positive 0 2566 2566 2462))
def path0340 : List Bool := [false,false,true,false,false,false,true,true,true,false,false,false,true,true,false,true,true,true,true,true,false,true,true,true,false,false,true,true,true,true,true,true,false,true,true,true,true]
theorem checked0340 : pathOK rootState path0340=true ∧ check axisLookup localCores (atPath rootState path0340) tree0340=true := by decide +kernel
end ThomsonNine.PackedMain
