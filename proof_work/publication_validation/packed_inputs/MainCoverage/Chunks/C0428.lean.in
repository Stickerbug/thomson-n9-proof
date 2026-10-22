import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0428 : Tree := (Tree.split 18 (Tree.split 18 (Tree.split 18 Tree.gram (Tree.split 18 Tree.gram (Tree.split 18 (Tree.split 18 Tree.gram (Tree.split 18 Tree.gram (Tree.positive 1 600 608 543))) (Tree.positive 1 344 348 544)))) (Tree.positive 1 199 201 310)) (Tree.positive 1 199 202 171))
def path0428 : List Bool := [false,false,true,false,false,false,true,true,true,false,true,false,true,false,false,true,false,true,true,false,false,false]
theorem checked0428 : pathOK rootState path0428=true ∧ check axisLookup localCores (atPath rootState path0428) tree0428=true := by decide +kernel
end ThomsonNine.PackedMain
