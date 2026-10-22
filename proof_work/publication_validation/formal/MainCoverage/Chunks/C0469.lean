import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0469 : Tree := (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.positive 0 109 109 101) (Tree.positive 0 109 110 101)) (Tree.positive 0 110 59 101)) (Tree.positive 0 59 59 102)) (Tree.positive 0 59 60 50)) (Tree.positive 0 60 29 50))
def path0469 : List Bool := [false,false,true,false,false,true,true,true,false,false,false,true,true,true,false]
theorem checked0469 : pathOK rootState path0469=true ∧ check axisLookup localCores (atPath rootState path0469) tree0469=true := by decide +kernel
end ThomsonNine.PackedMain
