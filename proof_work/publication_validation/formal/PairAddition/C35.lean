import PairAddition.Metadata
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.PairAddition
namespace C35
def contributions : List Contribution := [⟨135,0,18453790041575472822824759016955052032,[(-1),0,73]⟩,
⟨137,1,(-1347126673035009516066207408237718798336),[1,0,(-1)]⟩]
def diagonal : Fin 38 → ℤ := ![(-1328672882993434043243382649220763746304),
0,
96993120458520685156766933393115753480192,
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
0,
0,
0]
theorem contributions_valid : contributions.all (fun c => decide (Valid 35 c))=true := by decide +kernel
theorem features_complete : contributions.map Contribution.feature=
    (List.finRange 138).filter (fun f => decide (35≤(features f).order.val ∧ ((features f).order.val-35)%2=0)) := by decide +kernel
theorem matrix_identity : ∀ i j : Fin 38, matrixEntry contributions i j=if i=j then diagonal i else 0 := by decide +kernel
end C35
end ThomsonNine.PairAddition
