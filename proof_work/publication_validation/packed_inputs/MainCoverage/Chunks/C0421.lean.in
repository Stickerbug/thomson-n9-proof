import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0421 : Tree := (Tree.split 1 (Tree.positive 0 28 12 21) (Tree.split 1 (Tree.positive 0 29 28 21) (Tree.positive 0 29 29 21)))
def path0421 : List Bool := [false,false,true,false,false,false,true,true,true,false,false,true]
theorem checked0421 : pathOK rootState path0421=true ∧ check axisLookup localCores (atPath rootState path0421) tree0421=true := by decide +kernel
end ThomsonNine.PackedMain
