import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0389 : Tree := (Tree.positive 1 1029 1030 947)
def path0389 : List Bool := [false,false,true,false,false,false,true,true,true,false,false,false,true,true,false,true,true,true,true,true,false,true,true,true,true,true,true,false,false,false,false,true]
theorem checked0389 : pathOK rootState path0389=true ∧ check axisLookup localCores (atPath rootState path0389) tree0389=true := by decide +kernel
end ThomsonNine.PackedMain
