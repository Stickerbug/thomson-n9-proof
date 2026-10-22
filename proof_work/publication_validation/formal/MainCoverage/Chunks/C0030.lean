import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0030 : Tree := (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.positive 0 370 390 454)))))))) (Tree.split 17 (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.positive 0 370 224 262))))) (Tree.split 17 (Tree.split 17 (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.positive 0 368 392 264)))) (Tree.split 17 (Tree.split 17 Tree.gram (Tree.positive 0 368 224 263)) (Tree.positive 0 211 224 264))) (Tree.split 17 (Tree.split 17 (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.positive 0 370 392 263))) (Tree.positive 0 212 223 264)) (Tree.positive 0 212 224 148))))))))
def path0030 : List Bool := [false,false,false,false,true,true,true,false,true,true,false,true,true,false,false,false]
theorem checked0030 : pathOK rootState path0030=true ∧ check axisLookup localCores (atPath rootState path0030) tree0030=true := by decide +kernel
end ThomsonNine.PackedMain
