import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0468 : Tree := (Tree.split 1 (Tree.split 1 (Tree.positive 0 59 28 50) (Tree.order 0 1)) (Tree.split 1 (Tree.positive 0 59 28 51) (Tree.order 0 1)))
def path0468 : List Bool := [false,false,true,false,false,true,true,true,false,false,false,true,true,false]
theorem checked0468 : pathOK rootState path0468=true ∧ check axisLookup localCores (atPath rootState path0468) tree0468=true := by decide +kernel
end ThomsonNine.PackedMain
