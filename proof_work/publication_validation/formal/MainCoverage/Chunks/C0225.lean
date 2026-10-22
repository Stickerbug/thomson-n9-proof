import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0225 : Tree := (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.positive 0 1731 1763 1524)))))))))))))))))
def path0225 : List Bool := [false,false,true,false,false,false,true,true,false,true,true,true,false,false,true,false,false,false,false]
theorem checked0225 : pathOK rootState path0225=true ∧ check axisLookup localCores (atPath rootState path0225) tree0225=true := by decide +kernel
end ThomsonNine.PackedMain
