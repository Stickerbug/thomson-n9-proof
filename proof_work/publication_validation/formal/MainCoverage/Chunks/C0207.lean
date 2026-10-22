import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0207 : Tree := (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.positive 0 361 360 291)) (Tree.order 0 1)) (Tree.positive 0 208 207 292)) (Tree.positive 0 208 208 162))
def path0207 : List Bool := [false,false,true,false,false,false,true,true,false,true,true,true,false,false,false,true,true,false,true,true,true,true]
theorem checked0207 : pathOK rootState path0207=true ∧ check axisLookup localCores (atPath rootState path0207) tree0207=true := by decide +kernel
end ThomsonNine.PackedMain
