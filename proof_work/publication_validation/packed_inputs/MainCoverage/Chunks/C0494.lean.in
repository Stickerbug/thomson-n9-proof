import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0494 : Tree := (Tree.split 1 (Tree.positive 0 21 22 8) (Tree.split 1 (Tree.positive 0 21 23 22) (Tree.split 1 (Tree.split 1 (Tree.positive 0 46 50 23) (Tree.split 1 (Tree.positive 0 46 51 50) (Tree.split 1 (Tree.split 1 (Tree.positive 0 93 103 51) (Tree.split 1 (Tree.positive 0 93 104 103) (Tree.split 1 (Tree.split 1 (Tree.positive 0 177 189 104) (Tree.positive 0 177 190 104)) (Tree.positive 0 178 104 104)))) (Tree.split 1 (Tree.positive 0 94 103 51) (Tree.positive 0 94 104 51))))) (Tree.split 1 (Tree.positive 0 47 50 23) (Tree.split 1 (Tree.positive 0 47 51 50) (Tree.positive 0 47 51 51))))))
def path0494 : List Bool := [true,true,true,false,true,true,true,false,false,true]
theorem checked0494 : pathOK rootState path0494=true ∧ check axisLookup localCores (atPath rootState path0494) tree0494=true := by decide +kernel
end ThomsonNine.PackedMain
