import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0436 : Tree := (Tree.split 3 (Tree.split 3 (Tree.split 3 (Tree.split 3 (Tree.positive 1 343 201 311) (Tree.split 3 (Tree.split 3 (Tree.positive 1 344 347 547) (Tree.positive 0 344 347 548)) (Tree.positive 0 344 348 311))) (Tree.positive 0 199 201 312)) (Tree.positive 0 199 202 172)) (Tree.positive 0 200 113 172))
def path0436 : List Bool := [false,false,true,false,false,false,true,true,true,false,true,false,true,false,false,true,false,true,true,false,true]
theorem checked0436 : pathOK rootState path0436=true ∧ check axisLookup localCores (atPath rootState path0436) tree0436=true := by decide +kernel
end ThomsonNine.PackedMain
