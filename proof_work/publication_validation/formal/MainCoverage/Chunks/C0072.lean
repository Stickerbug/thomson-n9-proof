import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0072 : Tree := (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 1 2) (Tree.positive 0 14 16 15)) (Tree.order 1 2)) (Tree.positive 0 15 5 4)) (Tree.positive 0 4 5 5))
def path0072 : List Bool := [false,false,false,true,true,true,false,true]
theorem checked0072 : pathOK rootState path0072=true ∧ check axisLookup localCores (atPath rootState path0072) tree0072=true := by decide +kernel
end ThomsonNine.PackedMain
