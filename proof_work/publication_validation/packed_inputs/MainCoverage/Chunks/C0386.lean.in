import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0386 : Tree := (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.local 6) (Tree.positive 0 3114 3115 2992)) (Tree.positive 0 3115 2567 2992)) (Tree.positive 0 2567 2567 2993)) (Tree.positive 0 2567 2568 2460)) (Tree.positive 0 2568 1692 2460))
def path0386 : List Bool := [false,false,true,false,false,false,true,true,true,false,false,false,true,true,false,true,true,true,true,true,false,true,true,true,true,true,true,false,false,false,false,false,true,false,false,true]
theorem checked0386 : pathOK rootState path0386=true ∧ check axisLookup localCores (atPath rootState path0386) tree0386=true := by decide +kernel
end ThomsonNine.PackedMain
