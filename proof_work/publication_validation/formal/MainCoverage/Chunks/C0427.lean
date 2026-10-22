import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0427 : Tree := (Tree.positive 1 111 61 90)
def path0427 : List Bool := [false,false,true,false,false,false,true,true,true,false,true,false,true,false,false,true,false,true,false]
theorem checked0427 : pathOK rootState path0427=true ∧ check axisLookup localCores (atPath rootState path0427) tree0427=true := by decide +kernel
end ThomsonNine.PackedMain
