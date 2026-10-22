import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0159 : Tree := (Tree.split 17 (Tree.split 16 Tree.gram (Tree.order 0 1)) (Tree.split 17 (Tree.split 17 (Tree.order 0 1) (Tree.split 17 (Tree.split 16 (Tree.split 16 (Tree.order 0 1) (Tree.split 16 Tree.gram (Tree.split 16 Tree.gram (Tree.order 0 1)))) (Tree.order 0 1)) (Tree.split 17 (Tree.split 17 (Tree.order 0 1) (Tree.split 17 (Tree.split 16 (Tree.split 16 (Tree.order 0 1) (Tree.split 16 Tree.gram (Tree.split 16 (Tree.split 16 (Tree.order 0 1) (Tree.split 16 Tree.gram (Tree.split 16 Tree.gram (Tree.order 0 1)))) (Tree.order 0 1)))) (Tree.order 0 1)) (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.positive 0 1844 1843 1395)) (Tree.order 0 1)) (Tree.positive 0 1105 1104 1396))) (Tree.order 0 1)))) (Tree.order 0 1)))) (Tree.order 0 1)))
def path0159 : List Bool := [false,false,true,false,false,false,true,true,false,true,true,false,true,true,true,false,false,false,false,false,true,true,false]
theorem checked0159 : pathOK rootState path0159=true ∧ check axisLookup localCores (atPath rootState path0159) tree0159=true := by decide +kernel
end ThomsonNine.PackedMain
