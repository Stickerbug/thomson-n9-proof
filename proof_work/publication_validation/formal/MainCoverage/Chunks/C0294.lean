import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0294 : Tree := (Tree.split 18 Tree.gram (Tree.positive 1 112 111 172))
def path0294 : List Bool := [false,false,true,false,false,false,true,true,true,false,false,false,true,true,false,true,true,true,true,false]
theorem checked0294 : pathOK rootState path0294=true ∧ check axisLookup localCores (atPath rootState path0294) tree0294=true := by decide +kernel
end ThomsonNine.PackedMain
