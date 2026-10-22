import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0174 : Tree := (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.positive 0 641 640 495)) (Tree.order 0 1)) (Tree.positive 0 365 364 496))) (Tree.order 0 1)) (Tree.positive 0 210 209 286)) (Tree.positive 0 210 210 159))
def path0174 : List Bool := [false,false,true,false,false,false,true,true,false,true,true,false,true,true,true,false,false,true,false,false,false,true]
theorem checked0174 : pathOK rootState path0174=true ∧ check axisLookup localCores (atPath rootState path0174) tree0174=true := by decide +kernel
end ThomsonNine.PackedMain
