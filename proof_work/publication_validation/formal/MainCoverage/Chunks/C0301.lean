import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0301 : Tree := (Tree.split 18 (Tree.split 16 Tree.gram (Tree.order 0 1)) (Tree.split 18 (Tree.split 18 (Tree.order 0 1) (Tree.split 18 (Tree.split 16 Tree.gram (Tree.order 0 1)) (Tree.split 18 (Tree.split 18 (Tree.order 0 1) (Tree.split 18 (Tree.split 16 Tree.gram (Tree.order 0 1)) (Tree.split 18 (Tree.split 18 (Tree.order 0 1) (Tree.split 18 (Tree.split 16 Tree.gram (Tree.order 0 1)) (Tree.split 18 (Tree.split 18 (Tree.order 0 1) (Tree.split 18 (Tree.split 18 (Tree.split 18 (Tree.order 0 1) (Tree.split 18 Tree.gram (Tree.positive 1 3450 3449 3476))) (Tree.order 0 1)) (Tree.positive 1 3130 3129 3229))) (Tree.order 0 1)))) (Tree.order 0 1)))) (Tree.order 0 1)))) (Tree.order 0 1)))
def path0301 : List Bool := [false,false,true,false,false,false,true,true,true,false,false,false,true,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true,false]
theorem checked0301 : pathOK rootState path0301=true ∧ check axisLookup localCores (atPath rootState path0301) tree0301=true := by decide +kernel
end ThomsonNine.PackedMain
