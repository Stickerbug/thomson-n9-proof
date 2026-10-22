import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0460 : Tree := (Tree.positive 0 30 30 45)
def path0460 : List Bool := [false,false,true,false,false,false,true,true,true,true,true,false,false,false,true]
theorem checked0460 : pathOK rootState path0460=true ∧ check axisLookup localCores (atPath rootState path0460) tree0460=true := by decide +kernel
end ThomsonNine.PackedMain
