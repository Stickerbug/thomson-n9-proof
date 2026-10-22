import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0388 : Tree := (Tree.positive 0 1693 1029 1601)
def path0388 : List Bool := [false,false,true,false,false,false,true,true,true,false,false,false,true,true,false,true,true,true,true,true,false,true,true,true,true,true,true,false,false,false,false,false,true,true]
theorem checked0388 : pathOK rootState path0388=true ∧ check axisLookup localCores (atPath rootState path0388) tree0388=true := by decide +kernel
end ThomsonNine.PackedMain
