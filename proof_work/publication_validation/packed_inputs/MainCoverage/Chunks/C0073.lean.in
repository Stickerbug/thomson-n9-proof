import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0073 : Tree := (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.positive 0 16 15 4)) (Tree.order 0 1)) (Tree.positive 0 5 4 5)) (Tree.split 1 (Tree.positive 0 5 5 4) (Tree.positive 0 5 5 5)))
def path0073 : List Bool := [false,false,false,true,true,true,true]
theorem checked0073 : pathOK rootState path0073=true ∧ check axisLookup localCores (atPath rootState path0073) tree0073=true := by decide +kernel
end ThomsonNine.PackedMain
