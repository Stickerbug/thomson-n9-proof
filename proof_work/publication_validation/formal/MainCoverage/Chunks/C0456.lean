import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0456 : Tree := (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.positive 0 203 202 169)) (Tree.order 0 1)) (Tree.positive 0 114 113 170)) (Tree.positive 0 114 114 89))
def path0456 : List Bool := [false,false,true,false,false,false,true,true,true,true,true,false,false,false,false,false,false,false,true]
theorem checked0456 : pathOK rootState path0456=true ∧ check axisLookup localCores (atPath rootState path0456) tree0456=true := by decide +kernel
end ThomsonNine.PackedMain
