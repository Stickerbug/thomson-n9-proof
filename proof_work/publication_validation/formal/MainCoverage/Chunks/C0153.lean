import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0153 : Tree := (Tree.positive 0 64 64 82)
def path0153 : List Bool := [false,false,true,false,false,false,true,true,false,true,true,false,true,true,false,true,true,true]
theorem checked0153 : pathOK rootState path0153=true ∧ check axisLookup localCores (atPath rootState path0153) tree0153=true := by decide +kernel
end ThomsonNine.PackedMain
