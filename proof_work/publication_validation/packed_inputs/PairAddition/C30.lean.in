import PairAddition.Metadata
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.PairAddition
namespace C30
def contributions : List Contribution := [⟨130,0,72040974595862608233623906143961088,[0,(-35),0,2415,0,(-34293),0,119209]⟩,
⟨132,1,(-10916326503467181106459716601579044864),[0,15,0,(-725),0,5893,0,(-5183)]⟩,
⟨134,2,3646930256966352816610743000725742157824,[0,(-3),0,79,0,(-149),0,73]⟩,
⟨136,3,(-250565561184511769988314577932215696490496),[0,1,0,(-3),0,3,0,(-1)]⟩]
def diagonal : Fin 38 → ℤ := ![0,
(-220111112141214778692685137876012949831680),
0,
15187666737743819729795274513444893538385920,
0,
(-215664867675962240163092898090917488245080064),
0,
749692159064059215805037217173189363899564032,
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
theorem contributions_valid : contributions.all (fun c => decide (Valid 30 c))=true := by decide +kernel
theorem features_complete : contributions.map Contribution.feature=
    (List.finRange 138).filter (fun f => decide (30≤(features f).order.val ∧ ((features f).order.val-30)%2=0)) := by decide +kernel
theorem matrix_identity : ∀ i j : Fin 38, matrixEntry contributions i j=if i=j then diagonal i else 0 := by decide +kernel
end C30
end ThomsonNine.PairAddition
