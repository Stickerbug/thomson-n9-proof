import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0317 : Tree := (Tree.split 19 (Tree.split 16 Tree.gram (Tree.order 0 1)) (Tree.split 3 (Tree.split 3 (Tree.order 0 1) (Tree.split 3 (Tree.split 2 (Tree.positive 1 3696 3415 3557) (Tree.order 0 1)) (Tree.split 3 (Tree.split 3 (Tree.order 0 1) (Tree.split 3 (Tree.split 2 (Tree.positive 1 3968 3695 3836) (Tree.order 0 1)) (Tree.split 3 (Tree.split 3 (Tree.order 0 1) (Tree.split 3 (Tree.split 2 (Tree.positive 1 4233 3967 4115) (Tree.order 0 1)) (Tree.split 3 (Tree.split 3 (Tree.order 0 1) (Tree.split 3 (Tree.split 3 (Tree.split 3 (Tree.order 0 1) (Tree.split 3 (Tree.positive 1 4471 4470 4647) (Tree.positive 0 4471 4470 4648))) (Tree.order 0 1)) (Tree.positive 0 4233 4232 4392))) (Tree.order 0 1)))) (Tree.order 0 1)))) (Tree.order 0 1)))) (Tree.order 0 1)))
def path0317 : List Bool := [false,false,true,false,false,false,true,true,true,false,false,false,true,true,false,true,true,true,true,true,false,true,true,true,false,false,true,true,true,false,true,true,true,true,true,true,true,true,true,true,false]
theorem checked0317 : pathOK rootState path0317=true ∧ check axisLookup localCores (atPath rootState path0317) tree0317=true := by decide +kernel
end ThomsonNine.PackedMain
