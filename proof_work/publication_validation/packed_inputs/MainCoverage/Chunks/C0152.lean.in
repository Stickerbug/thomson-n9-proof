import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0152 : Tree := (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.positive 0 375 374 273)) (Tree.order 0 1)) (Tree.positive 0 215 214 274))) (Tree.order 0 1)) (Tree.positive 0 120 119 154)) (Tree.positive 0 120 120 81))
def path0152 : List Bool := [false,false,true,false,false,false,true,true,false,true,true,false,true,true,false,true,true,false,true]
theorem checked0152 : pathOK rootState path0152=true ∧ check axisLookup localCores (atPath rootState path0152) tree0152=true := by decide +kernel
end ThomsonNine.PackedMain
