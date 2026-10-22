import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0452 : Tree := (Tree.split 3 (Tree.split 3 (Tree.split 3 (Tree.split 3 (Tree.order 0 1) (Tree.split 3 (Tree.split 2 (Tree.split 2 (Tree.order 0 1) (Tree.positive 1 1037 1036 937)) (Tree.order 0 1)) (Tree.positive 0 607 606 938))) (Tree.order 0 1)) (Tree.positive 1 348 347 542)) (Tree.positive 0 348 348 308))
def path0452 : List Bool := [false,false,true,false,false,false,true,true,true,true,true,false,false,false,false,false,false,false,false,false,true,false,false,true,true]
theorem checked0452 : pathOK rootState path0452=true ∧ check axisLookup localCores (atPath rootState path0452) tree0452=true := by decide +kernel
end ThomsonNine.PackedMain
