import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0051 : Tree := (Tree.split 16 (Tree.split 16 Tree.gram (Tree.order 0 1)) (Tree.split 16 (Tree.split 16 (Tree.order 0 1) (Tree.split 16 Tree.gram (Tree.split 16 (Tree.split 16 (Tree.order 0 1) (Tree.split 16 Tree.gram (Tree.split 16 (Tree.split 16 (Tree.order 0 1) (Tree.split 16 Tree.gram (Tree.split 16 Tree.gram (Tree.order 0 1)))) (Tree.order 0 1)))) (Tree.order 0 1)))) (Tree.order 0 1)))
def path0051 : List Bool := [false,false,false,true,true,true,false,false,true,false,false,false,false,false,true,true,false]
theorem checked0051 : pathOK rootState path0051=true ∧ check axisLookup localCores (atPath rootState path0051) tree0051=true := by decide +kernel
end ThomsonNine.PackedMain
