import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0019 : Tree := (Tree.split 17 (Tree.split 16 (Tree.split 16 (Tree.order 0 1) (Tree.split 16 Tree.gram (Tree.split 16 Tree.gram (Tree.order 0 1)))) (Tree.order 0 1)) (Tree.split 17 (Tree.split 17 (Tree.order 0 1) (Tree.split 17 (Tree.split 17 (Tree.split 17 (Tree.order 0 1) (Tree.split 17 (Tree.split 16 Tree.gram (Tree.order 0 1)) (Tree.split 17 (Tree.split 17 (Tree.order 0 1) (Tree.split 17 (Tree.split 16 Tree.gram (Tree.order 0 1)) (Tree.split 17 (Tree.split 17 (Tree.order 0 1) (Tree.split 17 Tree.gram (Tree.split 17 (Tree.split 17 (Tree.order 0 1) (Tree.split 17 Tree.gram (Tree.positive 0 1924 1923 2000))) (Tree.order 0 1)))) (Tree.order 0 1)))) (Tree.order 0 1)))) (Tree.order 0 1)) (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.positive 0 1145 1144 793)) (Tree.order 0 1)) (Tree.positive 0 661 660 794))) (Tree.order 0 1)) (Tree.positive 0 375 374 470))) (Tree.order 0 1)))) (Tree.order 0 1)))
def path0019 : List Bool := [false,false,false,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false]
theorem checked0019 : pathOK rootState path0019=true ∧ check axisLookup localCores (atPath rootState path0019) tree0019=true := by decide +kernel
end ThomsonNine.PackedMain
