import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0424 : Tree := (Tree.split 18 Tree.gram (Tree.split 18 (Tree.split 18 Tree.gram (Tree.split 18 Tree.gram (Tree.split 18 Tree.gram (Tree.positive 1 198 204 306)))) (Tree.positive 1 111 114 170)))
def path0424 : List Bool := [false,false,true,false,false,false,true,true,true,false,true,false,true,false,false,true,false,false,false]
theorem checked0424 : pathOK rootState path0424=true ∧ check axisLookup localCores (atPath rootState path0424) tree0424=true := by decide +kernel
end ThomsonNine.PackedMain
