import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0091 : Tree := (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.positive 0 628 652 844))))))))))))
def path0091 : List Bool := [false,false,true,false,false,false,true,true,false,true,true,false,false,true,true,true,false,false,false]
theorem checked0091 : pathOK rootState path0091=true ∧ check axisLookup localCores (atPath rootState path0091) tree0091=true := by decide +kernel
end ThomsonNine.PackedMain
