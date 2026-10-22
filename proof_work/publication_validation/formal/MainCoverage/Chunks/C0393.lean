import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0393 : Tree := (Tree.positive 0 604 346 546)
def path0393 : List Bool := [false,false,true,false,false,false,true,true,true,false,false,false,true,true,false,true,true,true,true,true,false,true,true,true,true,true,true,true]
theorem checked0393 : pathOK rootState path0393=true ∧ check axisLookup localCores (atPath rootState path0393) tree0393=true := by decide +kernel
end ThomsonNine.PackedMain
