import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0224 : Tree := (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.positive 0 629 628 511)) (Tree.order 0 1)) (Tree.positive 0 359 358 512))) (Tree.order 0 1)) (Tree.positive 0 207 206 294))) (Tree.order 0 1)) (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.positive 0 207 206 164)) (Tree.order 0 1))) (Tree.positive 0 116 116 86))
def path0224 : List Bool := [false,false,true,false,false,false,true,true,false,true,true,true,false,false,false,true,true,true,true]
theorem checked0224 : pathOK rootState path0224=true ∧ check axisLookup localCores (atPath rootState path0224) tree0224=true := by decide +kernel
end ThomsonNine.PackedMain
