import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0314 : Tree := (Tree.positive 1 2566 2565 2460)
def path0314 : List Bool := [false,false,true,false,false,false,true,true,true,false,false,false,true,true,false,true,true,true,true,true,false,true,true,true,false,false,true,true,true,false,true,true,true,true,true,true,true,false]
theorem checked0314 : pathOK rootState path0314=true ∧ check axisLookup localCores (atPath rootState path0314) tree0314=true := by decide +kernel
end ThomsonNine.PackedMain
