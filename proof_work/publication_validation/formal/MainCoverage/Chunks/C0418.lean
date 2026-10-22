import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0418 : Tree := (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.positive 0 345 344 313)) (Tree.order 0 1)) (Tree.positive 0 200 199 314)) (Tree.positive 0 200 200 173))
def path0418 : List Bool := [false,false,true,false,false,false,true,true,true,false,false,false,true,true,true,true,true,false,true,true,false,true]
theorem checked0418 : pathOK rootState path0418=true ∧ check axisLookup localCores (atPath rootState path0418) tree0418=true := by decide +kernel
end ThomsonNine.PackedMain
