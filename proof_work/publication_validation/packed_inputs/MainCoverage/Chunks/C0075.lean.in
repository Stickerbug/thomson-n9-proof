import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0075 : Tree := (Tree.split 17 Tree.gram (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.positive 0 12 11 7)) (Tree.order 0 1)))
def path0075 : List Bool := [false,false,true,false,false,false,true,false]
theorem checked0075 : pathOK rootState path0075=true ∧ check axisLookup localCores (atPath rootState path0075) tree0075=true := by decide +kernel
end ThomsonNine.PackedMain
