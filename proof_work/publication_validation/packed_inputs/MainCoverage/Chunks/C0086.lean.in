import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0086 : Tree := (Tree.split 16 Tree.gram (Tree.split 16 Tree.gram (Tree.order 0 1)))
def path0086 : List Bool := [false,false,true,false,false,false,true,true,false,true,true,false,false,false,true,true,true,true,true,true,true,true,false]
theorem checked0086 : pathOK rootState path0086=true ∧ check axisLookup localCores (atPath rootState path0086) tree0086=true := by decide +kernel
end ThomsonNine.PackedMain
