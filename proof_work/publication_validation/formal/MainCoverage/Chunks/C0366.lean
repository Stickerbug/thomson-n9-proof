import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0366 : Tree := (Tree.split 18 (Tree.split 16 (Tree.split 16 (Tree.order 0 1) (Tree.split 16 Tree.gram (Tree.split 16 Tree.gram (Tree.order 0 1)))) (Tree.order 0 1)) (Tree.split 18 (Tree.split 18 (Tree.order 0 1) (Tree.split 18 (Tree.split 16 (Tree.split 16 (Tree.order 0 1) (Tree.split 16 Tree.gram (Tree.split 16 (Tree.split 16 (Tree.order 0 1) (Tree.split 16 Tree.gram (Tree.split 16 Tree.gram (Tree.order 0 1)))) (Tree.order 0 1)))) (Tree.order 0 1)) (Tree.split 18 (Tree.split 18 (Tree.order 0 1) (Tree.split 18 (Tree.split 18 (Tree.split 18 (Tree.order 0 1) (Tree.split 18 (Tree.split 18 (Tree.split 18 (Tree.order 0 1) (Tree.split 18 Tree.gram (Tree.split 18 (Tree.split 18 (Tree.order 0 1) (Tree.split 18 Tree.gram (Tree.positive 1 4281 4280 4300))) (Tree.order 0 1)))) (Tree.order 0 1)) (Tree.split 2 (Tree.split 2 (Tree.order 0 1) (Tree.positive 1 3992 3991 3811)) (Tree.order 0 1)))) (Tree.order 0 1)) (Tree.split 2 (Tree.split 2 (Tree.order 0 1) (Tree.positive 1 3708 3707 3544)) (Tree.order 0 1)))) (Tree.order 0 1)))) (Tree.order 0 1)))
def path0366 : List Bool := [false,false,true,false,false,false,true,true,true,false,false,false,true,true,false,true,true,true,true,true,false,true,true,true,true,true,true,false,false,false,false,false,false,false,false,true,true,false]
theorem checked0366 : pathOK rootState path0366=true ∧ check axisLookup localCores (atPath rootState path0366) tree0366=true := by decide +kernel
end ThomsonNine.PackedMain
