import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0441 : Tree := (Tree.positive 0 12 13 21)
def path0441 : List Bool := [false,false,true,false,false,false,true,true,true,false,true,true]
theorem checked0441 : pathOK rootState path0441=true ∧ check axisLookup localCores (atPath rootState path0441) tree0441=true := by decide +kernel
end ThomsonNine.PackedMain
