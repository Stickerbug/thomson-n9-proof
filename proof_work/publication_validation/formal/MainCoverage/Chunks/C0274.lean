import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0274 : Tree := (Tree.split 17 (Tree.split 17 (Tree.split 17 (Tree.split 17 (Tree.split 17 (Tree.split 17 (Tree.split 17 (Tree.split 17 (Tree.split 17 (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.positive 0 1733 1073 1510))) (Tree.split 17 (Tree.split 17 Tree.gram (Tree.positive 0 1733 1074 1509)) (Tree.positive 0 1049 1074 1510))) (Tree.split 17 (Tree.split 17 (Tree.split 17 (Tree.split 17 Tree.gram (Tree.positive 0 1734 1781 1509)) (Tree.positive 0 1735 1073 1509)) (Tree.positive 0 1050 1073 1510)) (Tree.positive 0 1050 1074 901))) (Tree.positive 0 613 625 902)) (Tree.positive 0 613 626 523)) (Tree.positive 0 614 357 523)) (Tree.positive 0 351 357 524)) (Tree.positive 0 351 358 299)) (Tree.positive 0 352 206 299)) (Tree.positive 0 203 206 300))
def path0274 : List Bool := [false,false,true,false,false,false,true,true,false,true,true,true,false,false,true,false,true,false,true,false,true,false,true]
theorem checked0274 : pathOK rootState path0274=true ∧ check axisLookup localCores (atPath rootState path0274) tree0274=true := by decide +kernel
end ThomsonNine.PackedMain
