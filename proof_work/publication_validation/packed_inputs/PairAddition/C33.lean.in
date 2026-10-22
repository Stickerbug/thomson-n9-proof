import PairAddition.Metadata
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.PairAddition
namespace C33
def contributions : List Contribution := [⟨133,0,389868803695256468087847021484965888,[3,0,(-426),0,5183]⟩,
⟨135,1,(-161470662863785387199716641398356705280),[(-1),0,74,0,(-73)]⟩,
⟨137,2,5725288360398790443281381485010304892928,[1,0,(-2),0,1]⟩]
def diagonal : Fin 38 → ℤ := ![5567326516768262364294455466805312880640,
0,
(-790560365381093255729812676286354429050880),
0,
9618484445469967944712720894817312220119040,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0,
0]
theorem contributions_valid : contributions.all (fun c => decide (Valid 33 c))=true := by decide +kernel
theorem features_complete : contributions.map Contribution.feature=
    (List.finRange 138).filter (fun f => decide (33≤(features f).order.val ∧ ((features f).order.val-33)%2=0)) := by decide +kernel
theorem matrix_identity : ∀ i j : Fin 38, matrixEntry contributions i j=if i=j then diagonal i else 0 := by decide +kernel
end C33
end ThomsonNine.PairAddition
