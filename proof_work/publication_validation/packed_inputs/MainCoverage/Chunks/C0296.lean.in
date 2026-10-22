import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0296 : Tree := (Tree.split 16 Tree.gram (Tree.split 16 Tree.gram (Tree.order 0 1)))
def path0296 : List Bool := [false,false,true,false,false,false,true,true,true,false,false,false,true,true,false,true,true,true,true,true,false,true,false]
theorem checked0296 : pathOK rootState path0296=true ∧ check axisLookup localCores (atPath rootState path0296) tree0296=true := by decide +kernel
end ThomsonNine.PackedMain
