import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0487 : Tree := (Tree.split 1 (Tree.split 1 (Tree.positive 0 6 0 0) (Tree.split 1 (Tree.positive 0 7 6 0) (Tree.positive 0 7 7 0))) (Tree.split 1 (Tree.split 1 (Tree.positive 0 6 6 1) (Tree.split 1 (Tree.positive 0 6 7 8) (Tree.positive 0 6 7 9))) (Tree.split 1 (Tree.split 1 (Tree.positive 0 7 6 8) (Tree.positive 0 7 6 9)) (Tree.split 1 (Tree.positive 0 7 7 8) (Tree.positive 0 7 7 9)))))
def path0487 : List Bool := [true,true,true,false,false]
theorem checked0487 : pathOK rootState path0487=true ∧ check axisLookup localCores (atPath rootState path0487) tree0487=true := by decide +kernel
end ThomsonNine.PackedMain
