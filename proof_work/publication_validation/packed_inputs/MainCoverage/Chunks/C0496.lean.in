import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0496 : Tree := (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 1 2) (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 1 2) (Tree.positive 0 44 52 51)) (Tree.order 1 2)) (Tree.split 1 (Tree.split 1 (Tree.order 1 2) (Tree.positive 0 45 52 51)) (Tree.order 1 2)))) (Tree.order 1 2)) (Tree.split 1 (Tree.split 1 (Tree.order 1 2) (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 1 2) (Tree.positive 0 46 52 51)) (Tree.order 1 2)) (Tree.positive 0 47 24 23))) (Tree.order 1 2))) (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.positive 0 44 24 24) (Tree.split 1 (Tree.positive 0 45 52 24) (Tree.positive 0 45 53 24))) (Tree.positive 0 20 24 25)) (Tree.positive 0 20 25 9)) (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.positive 0 46 52 24) (Tree.positive 0 46 53 24)) (Tree.positive 0 47 24 24)) (Tree.positive 0 21 24 25)) (Tree.positive 0 21 25 9))))
def path0496 : List Bool := [true,true,true,false,true,true,true,true]
theorem checked0496 : pathOK rootState path0496=true ∧ check axisLookup localCores (atPath rootState path0496) tree0496=true := by decide +kernel
end ThomsonNine.PackedMain
