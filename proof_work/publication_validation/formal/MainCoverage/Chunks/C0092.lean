import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0092 : Tree := (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.positive 0 1825 1859 1396))))) (Tree.split 17 (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.positive 0 1827 1857 2124))))) (Tree.split 17 (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.positive 0 1827 1859 1395))) (Tree.positive 0 1096 1112 1396))))))))))))))
def path0092 : List Bool := [false,false,true,false,false,false,true,true,false,true,true,false,false,true,true,true,false,false,true,false]
theorem checked0092 : pathOK rootState path0092=true ∧ check axisLookup localCores (atPath rootState path0092) tree0092=true := by decide +kernel
end ThomsonNine.PackedMain
