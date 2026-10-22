import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0049 : Tree := (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.positive 0 698 700 713)))))) (Tree.split 17 (Tree.split 16 Tree.gram (Tree.split 16 Tree.gram (Tree.order 0 1))) (Tree.split 17 (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.positive 0 700 700 421))) (Tree.split 17 (Tree.split 17 (Tree.split 17 Tree.gram (Tree.positive 0 699 699 713)) (Tree.positive 0 699 700 422)) (Tree.positive 0 700 394 422))))))))))))))
def path0049 : List Bool := [false,false,false,true,true,true,false,false,true,false,false,false,false,false,false]
theorem checked0049 : pathOK rootState path0049=true ∧ check axisLookup localCores (atPath rootState path0049) tree0049=true := by decide +kernel
end ThomsonNine.PackedMain
