import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0287 : Tree := (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.positive 0 209 208 161)) (Tree.order 0 1)) (Tree.positive 0 117 116 162))) (Tree.order 0 1)) (Tree.positive 0 63 62 86))) (Tree.order 0 1)) (Tree.positive 0 31 30 43)) (Tree.positive 0 31 31 19))
def path0287 : List Bool := [false,false,true,false,false,false,true,true,false,true,true,true,true]
theorem checked0287 : pathOK rootState path0287=true ∧ check axisLookup localCores (atPath rootState path0287) tree0287=true := by decide +kernel
end ThomsonNine.PackedMain
