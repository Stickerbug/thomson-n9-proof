import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0408 : Tree := (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.positive 0 2559 2558 2473)) (Tree.order 0 1)) (Tree.positive 0 1688 1687 2474))) (Tree.order 0 1)) (Tree.positive 0 1027 1026 1609))) (Tree.order 0 1)) (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.positive 0 1027 1026 952)) (Tree.order 0 1))) (Tree.positive 0 602 602 548))
def path0408 : List Bool := [false,false,true,false,false,false,true,true,true,false,false,false,true,true,false,true,true,true,true,true,true,true,true,false,false,false,true,true]
theorem checked0408 : pathOK rootState path0408=true ∧ check axisLookup localCores (atPath rootState path0408) tree0408=true := by decide +kernel
end ThomsonNine.PackedMain
