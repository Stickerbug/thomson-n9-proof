import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0465 : Tree := (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.positive 0 12 11 8)) (Tree.order 0 1)) (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.positive 0 12 11 9)) (Tree.order 0 1)))
def path0465 : List Bool := [false,false,true,false,false,true,true,false]
theorem checked0465 : pathOK rootState path0465=true ∧ check axisLookup localCores (atPath rootState path0465) tree0465=true := by decide +kernel
end ThomsonNine.PackedMain
