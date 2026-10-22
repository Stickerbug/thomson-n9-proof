import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0410 : Tree := (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.positive 0 1029 1028 949)) (Tree.order 0 1)) (Tree.positive 0 603 602 950))) (Tree.order 0 1)) (Tree.positive 0 346 345 548)) (Tree.positive 0 346 346 311))
def path0410 : List Bool := [false,false,true,false,false,false,true,true,true,false,false,false,true,true,false,true,true,true,true,true,true,true,true,false,true]
theorem checked0410 : pathOK rootState path0410=true ∧ check axisLookup localCores (atPath rootState path0410) tree0410=true := by decide +kernel
end ThomsonNine.PackedMain
