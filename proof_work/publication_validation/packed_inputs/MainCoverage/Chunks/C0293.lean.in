import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0293 : Tree := (Tree.split 18 Tree.gram (Tree.split 18 Tree.gram (Tree.positive 1 111 112 172)))
def path0293 : List Bool := [false,false,true,false,false,false,true,true,true,false,false,false,true,true,false,true,true,true,false]
theorem checked0293 : pathOK rootState path0293=true ∧ check axisLookup localCores (atPath rootState path0293) tree0293=true := by decide +kernel
end ThomsonNine.PackedMain
