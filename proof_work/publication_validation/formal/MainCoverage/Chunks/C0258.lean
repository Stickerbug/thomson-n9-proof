import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0258 : Tree := (Tree.split 3 (Tree.split 3 (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.split 1 (Tree.split 1 (Tree.split 1 (Tree.order 0 1) (Tree.positive 0 1057 1056 909)) (Tree.order 0 1)) (Tree.positive 0 617 616 910))) (Tree.order 0 1)) (Tree.positive 0 353 352 528))) (Tree.order 0 1)) (Tree.positive 1 204 203 302)) (Tree.positive 0 204 204 167))
def path0258 : List Bool := [false,false,true,false,false,false,true,true,false,true,true,true,false,false,true,false,false,true,true,true,false,true]
theorem checked0258 : pathOK rootState path0258=true ∧ check axisLookup localCores (atPath rootState path0258) tree0258=true := by decide +kernel
end ThomsonNine.PackedMain
