import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0209 : Tree := (Tree.split 16 Tree.gram (Tree.split 16 (Tree.split 16 (Tree.order 0 1) (Tree.split 16 Tree.gram (Tree.split 16 Tree.gram (Tree.order 0 1)))) (Tree.order 0 1)))
def path0209 : List Bool := [false,false,true,false,false,false,true,true,false,true,true,true,false,false,false,true,true,true,false,false,false,true,false]
theorem checked0209 : pathOK rootState path0209=true ∧ check axisLookup localCores (atPath rootState path0209) tree0209=true := by decide +kernel
end ThomsonNine.PackedMain
