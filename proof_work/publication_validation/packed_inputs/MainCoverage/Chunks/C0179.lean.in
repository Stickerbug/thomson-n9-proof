import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0179 : Tree := (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.positive 0 119 118 83)) (Tree.order 0 1)) (Tree.positive 0 64 63 84)) (Tree.positive 0 64 64 41))
def path0179 : List Bool := [false,false,true,false,false,false,true,true,false,true,true,false,true,true,true,true]
theorem checked0179 : pathOK rootState path0179=true ∧ check axisLookup localCores (atPath rootState path0179) tree0179=true := by decide +kernel
end ThomsonNine.PackedMain
