import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0385 : Tree := (Tree.split 3 (Tree.split 3 (Tree.split 3 (Tree.split 3 (Tree.order 0 1) (Tree.split 3 (Tree.split 2 (Tree.split 2 (Tree.order 0 1) (Tree.positive 1 3422 3421 3270)) (Tree.order 0 1)) (Tree.positive 0 3116 3115 3271))) (Tree.order 0 1)) (Tree.positive 1 2568 2567 2991)) (Tree.positive 0 2568 2568 2459))
def path0385 : List Bool := [false,false,true,false,false,false,true,true,true,false,false,false,true,true,false,true,true,true,true,true,false,true,true,true,true,true,true,false,false,false,false,false,true,false,false,false,true]
theorem checked0385 : pathOK rootState path0385=true ∧ check axisLookup localCores (atPath rootState path0385) tree0385=true := by decide +kernel
end ThomsonNine.PackedMain
