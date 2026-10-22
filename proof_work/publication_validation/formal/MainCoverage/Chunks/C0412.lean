import MainCoverage.RootData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
def tree0412 : Tree := (Tree.split 19 (Tree.positive 1 59 59 45) (Tree.split 19 (Tree.split 19 Tree.gram (Tree.split 19 Tree.gram (Tree.split 19 Tree.gram (Tree.split 3 (Tree.positive 1 195 112 174) (Tree.split 3 (Tree.positive 1 196 199 174) (Tree.split 3 (Tree.positive 1 196 200 315) (Tree.split 3 (Tree.positive 1 337 200 316) (Tree.positive 0 338 200 316)))))))) (Tree.split 19 (Tree.split 3 (Tree.positive 1 109 111 92) (Tree.split 3 (Tree.positive 1 109 112 175) (Tree.positive 0 109 112 176))) (Tree.split 19 (Tree.split 19 (Tree.split 19 Tree.gram (Tree.split 19 Tree.gram (Tree.split 3 (Tree.positive 1 196 198 317) (Tree.split 3 (Tree.positive 1 337 198 318) (Tree.split 3 (Tree.positive 1 338 341 318) (Tree.positive 0 338 342 318)))))) (Tree.positive 0 110 111 176)) (Tree.split 3 (Tree.split 3 (Tree.split 3 (Tree.positive 1 195 199 175) (Tree.positive 0 195 200 175)) (Tree.split 3 (Tree.split 3 (Tree.split 3 (Tree.positive 1 337 199 317) (Tree.split 3 (Tree.positive 1 338 343 317) (Tree.positive 0 338 344 317))) (Tree.positive 0 196 199 318)) (Tree.positive 0 196 200 175))) (Tree.positive 0 110 112 176))))))
def path0412 : List Bool := [false,false,true,false,false,false,true,true,true,false,false,false,true,true,true,false]
theorem checked0412 : pathOK rootState path0412=true ∧ check axisLookup localCores (atPath rootState path0412) tree0412=true := by decide +kernel
end ThomsonNine.PackedMain
