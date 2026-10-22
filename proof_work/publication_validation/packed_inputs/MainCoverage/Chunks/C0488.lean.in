import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0488 : Tree := (Tree.split 1 (Tree.split 1 (Tree.positive 0 6 8 0) (Tree.order 1 2)) (Tree.split 1 (Tree.split 1 (Tree.order 1 2) (Tree.positive 0 7 8 7)) (Tree.order 1 2)))
def path0488 : List Bool := [true,true,true,false,true,false]
theorem checked0488 : pathOK rootState path0488=true ∧ check axisLookup localCores (atPath rootState path0488) tree0488=true := by decide +kernel
end ThomsonNine.PackedMain
