import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0413 : Tree := (Tree.split 17 (Tree.split 16 Tree.gram (Tree.order 0 1)) (Tree.split 17 (Tree.split 17 (Tree.order 0 1) (Tree.split 17 (Tree.split 16 Tree.gram (Tree.order 0 1)) (Tree.positive 0 111 110 176))) (Tree.order 0 1)))
def path0413 : List Bool := [false,false,true,false,false,false,true,true,true,false,false,false,true,true,true,true,false]
theorem checked0413 : pathOK rootState path0413=true ∧ check axisLookup localCores (atPath rootState path0413) tree0413=true := by decide +kernel
end ThomsonNine.PackedMain
