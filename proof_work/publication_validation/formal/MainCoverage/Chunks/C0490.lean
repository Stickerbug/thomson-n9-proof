import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0490 : Tree := (Tree.positive 0 20 22 8)
def path0490 : List Bool := [true,true,true,false,true,true,true,false,false,false,false]
theorem checked0490 : pathOK rootState path0490=true ∧ check axisLookup localCores (atPath rootState path0490) tree0490=true := by decide +kernel
end ThomsonNine.PackedMain
