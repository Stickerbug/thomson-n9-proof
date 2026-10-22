import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0181 : Tree := (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.positive 0 1063 1096 1460))) (Tree.split 17 (Tree.split 17 Tree.gram (Tree.positive 0 1064 1095 1460)) (Tree.positive 0 1064 1096 876)))))))))))))))
def path0181 : List Bool := [false,false,true,false,false,false,true,true,false,true,true,true,false,false,false,false,true,false]
theorem checked0181 : pathOK rootState path0181=true ∧ check axisLookup localCores (atPath rootState path0181) tree0181=true := by decide +kernel
end ThomsonNine.PackedMain
