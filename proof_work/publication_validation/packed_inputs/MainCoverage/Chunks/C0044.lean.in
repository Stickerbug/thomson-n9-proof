import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0044 : Tree := (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 1 2) (Tree.positive 0 12 16 15)) (Tree.order 1 2)) (Tree.split 1 (Tree.split 1 (Tree.order 1 2) (Tree.split 1 (Tree.positive 0 30 16 15) (Tree.positive 0 31 16 15))) (Tree.order 1 2))) (Tree.positive 0 3 5 5))
def path0044 : List Bool := [false,false,false,false,true,true,true,true]
theorem checked0044 : pathOK rootState path0044=true ∧ check axisLookup localCores (atPath rootState path0044) tree0044=true := by decide +kernel
end ThomsonNine.PackedMain
