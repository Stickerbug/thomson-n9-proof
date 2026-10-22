import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0374 : Tree := (Tree.split 16 (Tree.split 16 Tree.gram (Tree.order 0 1)) (Tree.split 16 (Tree.split 16 (Tree.order 0 1) (Tree.split 16 (Tree.split 16 Tree.gram (Tree.order 0 1)) (Tree.split 16 (Tree.split 16 (Tree.order 0 1) (Tree.split 16 Tree.gram (Tree.split 16 (Tree.split 16 (Tree.order 0 1) (Tree.split 16 Tree.gram (Tree.split 16 Tree.gram (Tree.order 0 1)))) (Tree.order 0 1)))) (Tree.order 0 1)))) (Tree.order 0 1)))
def path0374 : List Bool := [false,false,true,false,false,false,true,true,true,false,false,false,true,true,false,true,true,true,true,true,false,true,true,true,true,true,true,false,false,false,false,false,true,false,false,false,false,false,false,true,false]
theorem checked0374 : pathOK rootState path0374=true ∧ check axisLookup localCores (atPath rootState path0374) tree0374=true := by decide +kernel
end ThomsonNine.PackedMain
