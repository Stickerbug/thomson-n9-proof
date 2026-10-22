import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0025 : Tree := (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.positive 0 2 5 5)))
def path0025 : List Bool := [false,false,false,false,true,true,false]
theorem checked0025 : pathOK rootState path0025=true ∧ check axisLookup localCores (atPath rootState path0025) tree0025=true := by decide +kernel
end ThomsonNine.PackedMain
