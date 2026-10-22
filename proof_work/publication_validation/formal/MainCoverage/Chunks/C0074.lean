import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0074 : Tree := (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.positive 0 11 3 7))))
def path0074 : List Bool := [false,false,true,false,false,false,false]
theorem checked0074 : pathOK rootState path0074=true ∧ check axisLookup localCores (atPath rootState path0074) tree0074=true := by decide +kernel
end ThomsonNine.PackedMain
