import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0464 : Tree := (Tree.split 17 (Tree.split 1 (Tree.positive 0 2 2 8) (Tree.positive 0 2 2 9)) (Tree.split 17 (Tree.split 1 (Tree.split 1 (Tree.positive 0 10 12 8) (Tree.positive 0 10 13 8)) (Tree.split 1 (Tree.positive 0 11 12 8) (Tree.positive 0 11 13 8))) (Tree.split 17 (Tree.split 17 (Tree.positive 0 10 12 9) (Tree.split 17 (Tree.split 17 (Tree.split 17 (Tree.split 17 (Tree.split 17 Tree.gram (Tree.positive 0 56 30 52)) (Tree.positive 0 26 30 53)) (Tree.positive 0 26 31 24)) (Tree.positive 0 27 13 24)) (Tree.positive 0 10 13 25))) (Tree.split 1 (Tree.positive 0 11 12 9) (Tree.positive 0 11 13 9)))))
def path0464 : List Bool := [false,false,true,false,false,true,false]
theorem checked0464 : pathOK rootState path0464=true ∧ check axisLookup localCores (atPath rootState path0464) tree0464=true := by decide +kernel
end ThomsonNine.PackedMain
