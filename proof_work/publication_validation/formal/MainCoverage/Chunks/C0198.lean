import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0198 : Tree := (Tree.split 17 (Tree.split 16 Tree.gram (Tree.order 0 1)) (Tree.split 17 (Tree.split 17 (Tree.order 0 1) (Tree.split 17 (Tree.split 16 Tree.gram (Tree.order 0 1)) (Tree.split 17 (Tree.split 17 (Tree.order 0 1) (Tree.split 17 (Tree.split 16 (Tree.split 16 (Tree.order 0 1) (Tree.split 16 Tree.gram (Tree.split 16 Tree.gram (Tree.order 0 1)))) (Tree.order 0 1)) (Tree.split 17 (Tree.split 17 (Tree.order 0 1) (Tree.split 17 (Tree.split 17 (Tree.split 17 (Tree.order 0 1) (Tree.split 17 (Tree.split 16 Tree.gram (Tree.order 0 1)) (Tree.split 17 (Tree.split 17 (Tree.order 0 1) (Tree.split 17 (Tree.split 16 Tree.gram (Tree.order 0 1)) (Tree.positive 0 1796 1795 2215))) (Tree.order 0 1)))) (Tree.order 0 1)) (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.positive 0 1081 1080 876)) (Tree.order 0 1)))) (Tree.order 0 1)))) (Tree.order 0 1)))) (Tree.order 0 1)))
def path0198 : List Bool := [false,false,true,false,false,false,true,true,false,true,true,true,false,false,false,true,true,false,true,false]
theorem checked0198 : pathOK rootState path0198=true ∧ check axisLookup localCores (atPath rootState path0198) tree0198=true := by decide +kernel
end ThomsonNine.PackedMain
