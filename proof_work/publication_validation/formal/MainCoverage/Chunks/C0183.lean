import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0183 : Tree := Tree.gram
def path0183 : List Bool := [false,false,true,false,false,false,true,true,false,true,true,true,false,false,false,false,true,true,true,false,false]
theorem checked0183 : pathOK rootState path0183=true ∧ check axisLookup localCores (atPath rootState path0183) tree0183=true := by decide +kernel
end ThomsonNine.PackedMain
