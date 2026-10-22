import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0467 : Tree := (Tree.split 1 (Tree.positive 0 28 28 23) (Tree.split 1 (Tree.split 1 (Tree.positive 0 57 29 50) (Tree.split 1 (Tree.positive 0 58 59 50) (Tree.positive 0 58 60 50))) (Tree.split 1 (Tree.positive 0 57 29 51) (Tree.split 1 (Tree.positive 0 58 59 51) (Tree.split 1 (Tree.positive 0 58 60 103) (Tree.positive 0 58 60 104))))))
def path0467 : List Bool := [false,false,true,false,false,true,true,true,false,false,false,true,false]
theorem checked0467 : pathOK rootState path0467=true ∧ check axisLookup localCores (atPath rootState path0467) tree0467=true := by decide +kernel
end ThomsonNine.PackedMain
