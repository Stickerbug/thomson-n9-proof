import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0150 : Tree := (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.positive 0 373 372 275)) (Tree.order 0 1)) (Tree.positive 0 214 213 276)) (Tree.positive 0 214 214 154))
def path0150 : List Bool := [false,false,true,false,false,false,true,true,false,true,true,false,true,true,false,true,true,false,false,false,true,true]
theorem checked0150 : pathOK rootState path0150=true ∧ check axisLookup localCores (atPath rootState path0150) tree0150=true := by decide +kernel
end ThomsonNine.PackedMain
