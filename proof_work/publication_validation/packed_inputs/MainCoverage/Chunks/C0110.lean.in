import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0110 : Tree := Tree.gram
def path0110 : List Bool := [false,false,true,false,false,false,true,true,false,true,true,false,true,true,false,false,false,false]
theorem checked0110 : pathOK rootState path0110=true ∧ check axisLookup localCores (atPath rootState path0110) tree0110=true := by decide +kernel
end ThomsonNine.PackedMain
