import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0323 : Tree := (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.positive 0 3698 3697 3557)) (Tree.order 0 1)) (Tree.positive 0 3417 3416 3558)) (Tree.positive 0 3417 3417 3277))
def path0323 : List Bool := [false,false,true,false,false,false,true,true,true,false,false,false,true,true,false,true,true,true,true,true,false,true,true,true,false,false,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true]
theorem checked0323 : pathOK rootState path0323=true ∧ check axisLookup localCores (atPath rootState path0323) tree0323=true := by decide +kernel
end ThomsonNine.PackedMain
