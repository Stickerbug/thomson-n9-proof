import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0046 : Tree := (Tree.split 16 (Tree.split 16 (Tree.split 16 (Tree.order 0 2) (Tree.split 16 Tree.gram (Tree.order 0 2))) (Tree.order 1 2)) (Tree.order 0 2))
def path0046 : List Bool := [false,false,false,true,true,false]
theorem checked0046 : pathOK rootState path0046=true ∧ check axisLookup localCores (atPath rootState path0046) tree0046=true := by decide +kernel
end ThomsonNine.PackedMain
