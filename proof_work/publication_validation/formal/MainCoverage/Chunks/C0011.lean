import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0011 : Tree := (Tree.split 16 Tree.gram (Tree.split 16 Tree.gram (Tree.order 0 1)))
def path0011 : List Bool := [false,false,false,false,false,true,true,true,true,true,true,true,true,true,true,true,false]
theorem checked0011 : pathOK rootState path0011=true ∧ check axisLookup localCores (atPath rootState path0011) tree0011=true := by decide +kernel
end ThomsonNine.PackedMain
