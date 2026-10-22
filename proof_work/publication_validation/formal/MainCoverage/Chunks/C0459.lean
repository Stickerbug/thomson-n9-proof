import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0459 : Tree := (Tree.positive 0 62 30 44)
def path0459 : List Bool := [false,false,true,false,false,false,true,true,true,true,true,false,false,false,false,true]
theorem checked0459 : pathOK rootState path0459=true ∧ check axisLookup localCores (atPath rootState path0459) tree0459=true := by decide +kernel
end ThomsonNine.PackedMain
