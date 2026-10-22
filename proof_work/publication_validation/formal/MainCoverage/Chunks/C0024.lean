import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0024 : Tree := (Tree.split 16 Tree.gram (Tree.split 16 Tree.gram (Tree.order 1 2)))
def path0024 : List Bool := [false,false,false,false,true,false]
theorem checked0024 : pathOK rootState path0024=true ∧ check axisLookup localCores (atPath rootState path0024) tree0024=true := by decide +kernel
end ThomsonNine.PackedMain
