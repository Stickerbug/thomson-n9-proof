import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0026 : Tree := (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.split 17 Tree.gram (Tree.positive 0 13 15 15))))
def path0026 : List Bool := [false,false,false,false,true,true,true,false,false]
theorem checked0026 : pathOK rootState path0026=true ∧ check axisLookup localCores (atPath rootState path0026) tree0026=true := by decide +kernel
end ThomsonNine.PackedMain
