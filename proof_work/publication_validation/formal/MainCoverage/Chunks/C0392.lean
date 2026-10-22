import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0392 : Tree := (Tree.positive 0 603 604 546)
def path0392 : List Bool := [false,false,true,false,false,false,true,true,true,false,false,false,true,true,false,true,true,true,true,true,false,true,true,true,true,true,true,false,true]
theorem checked0392 : pathOK rootState path0392=true ∧ check axisLookup localCores (atPath rootState path0392) tree0392=true := by decide +kernel
end ThomsonNine.PackedMain
