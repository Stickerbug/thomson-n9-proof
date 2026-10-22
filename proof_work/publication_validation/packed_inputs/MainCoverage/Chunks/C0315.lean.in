import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0315 : Tree := (Tree.split 16 Tree.gram (Tree.split 16 Tree.gram (Tree.local 6)))
def path0315 : List Bool := [false,false,true,false,false,false,true,true,true,false,false,false,true,true,false,true,true,true,true,true,false,true,true,true,false,false,true,true,true,false,true,true,true,true,true,true,true,true,false]
theorem checked0315 : pathOK rootState path0315=true ∧ check axisLookup localCores (atPath rootState path0315) tree0315=true := by decide +kernel
end ThomsonNine.PackedMain
