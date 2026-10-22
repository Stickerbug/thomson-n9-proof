import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0155 : Tree := (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.positive 0 1841 1843 2124)))))) (Tree.split 17 (Tree.split 16 Tree.gram (Tree.split 16 Tree.gram (Tree.order 0 1))) (Tree.split 17 (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 (Tree.split 17 Tree.gram (Tree.positive 0 2803 1843 2122)) (Tree.positive 0 1843 1843 2123)))) (Tree.split 17 (Tree.split 17 (Tree.split 17 Tree.gram (Tree.positive 0 1842 1842 2124)) (Tree.positive 0 1842 1843 1396)) (Tree.positive 0 1843 1104 1396))))))))))))
def path0155 : List Bool := [false,false,true,false,false,false,true,true,false,true,true,false,true,true,true,false,false,false,false,false,true,false,false]
theorem checked0155 : pathOK rootState path0155=true ∧ check axisLookup localCores (atPath rootState path0155) tree0155=true := by decide +kernel
end ThomsonNine.PackedMain
