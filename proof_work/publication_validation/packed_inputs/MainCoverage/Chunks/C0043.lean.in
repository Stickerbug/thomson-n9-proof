import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0043 : Tree := (Tree.split 1 (Tree.split 1 (Tree.positive 0 30 15 16) (Tree.positive 0 31 15 16)) (Tree.positive 0 13 15 17))
def path0043 : List Bool := [false,false,false,false,true,true,true,false,true,true,true]
theorem checked0043 : pathOK rootState path0043=true ∧ check axisLookup localCores (atPath rootState path0043) tree0043=true := by decide +kernel
end ThomsonNine.PackedMain
