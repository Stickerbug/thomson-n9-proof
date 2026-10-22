import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0349 : Tree := (Tree.split 16 Tree.gram (Tree.split 16 Tree.gram (Tree.order 0 1)))
def path0349 : List Bool := [false,false,true,false,false,false,true,true,true,false,false,false,true,true,false,true,true,true,true,true,false,true,true,true,true,true,false,false,false,false,true,false]
theorem checked0349 : pathOK rootState path0349=true ∧ check axisLookup localCores (atPath rootState path0349) tree0349=true := by decide +kernel
end ThomsonNine.PackedMain
