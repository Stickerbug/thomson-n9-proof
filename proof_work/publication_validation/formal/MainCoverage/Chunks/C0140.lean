import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0140 : Tree := (Tree.positive 0 118 120 82)
def path0140 : List Bool := [false,false,true,false,false,false,true,true,false,true,true,false,true,true,false,false,true,true,true,true]
theorem checked0140 : pathOK rootState path0140=true ∧ check axisLookup localCores (atPath rootState path0140) tree0140=true := by decide +kernel
end ThomsonNine.PackedMain
