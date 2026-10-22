import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0454 : Tree := (Tree.split 3 (Tree.split 3 (Tree.split 2 (Tree.split 2 (Tree.order 0 1) (Tree.positive 1 349 348 307)) (Tree.order 0 1)) (Tree.positive 0 202 201 308)) (Tree.positive 0 202 202 170))
def path0454 : List Bool := [false,false,true,false,false,false,true,true,true,true,true,false,false,false,false,false,false,false,false,false,true,true]
theorem checked0454 : pathOK rootState path0454=true ∧ check axisLookup localCores (atPath rootState path0454) tree0454=true := by decide +kernel
end ThomsonNine.PackedMain
