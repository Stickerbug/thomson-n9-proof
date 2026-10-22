import PairAddition.Metadata
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.PairAddition
namespace C37
def contributions : List Contribution := [⟨137,0,145635316003784812547698098187861491712,[1]⟩]
def diagonal : Fin 38 → ℤ := ![145635316003784812547698098187861491712,
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
0,
0,
0]
theorem contributions_valid : contributions.all (fun c => decide (Valid 37 c))=true := by decide +kernel
theorem features_complete : contributions.map Contribution.feature=
    (List.finRange 138).filter (fun f => decide (37≤(features f).order.val ∧ ((features f).order.val-37)%2=0)) := by decide +kernel
theorem matrix_identity : ∀ i j : Fin 38, matrixEntry contributions i j=if i=j then diagonal i else 0 := by decide +kernel
end C37
end ThomsonNine.PairAddition
