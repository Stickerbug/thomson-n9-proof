import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0495 : Tree := (Tree.split 1 (Tree.split 1 (Tree.positive 0 20 22 9) (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.positive 0 44 50 24) (Tree.positive 0 44 51 24)) (Tree.split 1 (Tree.positive 0 45 50 24) (Tree.positive 0 45 51 24))) (Tree.positive 0 20 23 25))) (Tree.split 1 (Tree.positive 0 21 22 9) (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.positive 0 46 50 24) (Tree.positive 0 46 51 24)) (Tree.positive 0 47 23 24)) (Tree.positive 0 21 23 25))))
def path0495 : List Bool := [true,true,true,false,true,true,true,false,true]
theorem checked0495 : pathOK rootState path0495=true ∧ check axisLookup localCores (atPath rootState path0495) tree0495=true := by decide +kernel
end ThomsonNine.PackedMain
