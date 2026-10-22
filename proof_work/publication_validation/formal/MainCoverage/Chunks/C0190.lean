import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0190 : Tree := (Tree.split 16 (Tree.split 16 Tree.gram (Tree.order 0 1)) (Tree.split 16 (Tree.split 16 (Tree.order 0 1) (Tree.split 16 Tree.gram (Tree.split 16 (Tree.split 16 (Tree.order 0 1) (Tree.split 16 Tree.gram (Tree.split 16 Tree.gram (Tree.order 0 1)))) (Tree.order 0 1)))) (Tree.order 0 1)))
def path0190 : List Bool := [false,false,true,false,false,false,true,true,false,true,true,true,false,false,false,true,false]
theorem checked0190 : pathOK rootState path0190=true ∧ check axisLookup localCores (atPath rootState path0190) tree0190=true := by decide +kernel
end ThomsonNine.PackedMain
