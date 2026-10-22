import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0461 : Tree := (Tree.positive 0 30 31 20)
def path0461 : List Bool := [false,false,true,false,false,false,true,true,true,true,true,false,false,true]
theorem checked0461 : pathOK rootState path0461=true ∧ check axisLookup localCores (atPath rootState path0461) tree0461=true := by decide +kernel
end ThomsonNine.PackedMain
