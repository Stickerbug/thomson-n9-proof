import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0226 : Tree := (Tree.split 16 Tree.gram (Tree.split 16 Tree.gram (Tree.order 0 1)))
def path0226 : List Bool := [false,false,true,false,false,false,true,true,false,true,true,true,false,false,true,false,false,false,true,false]
theorem checked0226 : pathOK rootState path0226=true ∧ check axisLookup localCores (atPath rootState path0226) tree0226=true := by decide +kernel
end ThomsonNine.PackedMain
