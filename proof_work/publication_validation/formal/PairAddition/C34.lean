import PairAddition.Metadata
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.PairAddition
namespace C34
def contributions : List Contribution := [⟨134,0,110722740249452836936948554101730312192,[0,(-3),0,73]⟩,
⟨136,1,(-24248280114630171289191733348278938370048),[0,1,0,(-1)]⟩]
def diagonal : Fin 38 → ℤ := ![0,
(-23251775452385095756759196361363365560320),
0,
565793202674703996747807111459841895301120,
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
theorem contributions_valid : contributions.all (fun c => decide (Valid 34 c))=true := by decide +kernel
theorem features_complete : contributions.map Contribution.feature=
    (List.finRange 138).filter (fun f => decide (34≤(features f).order.val ∧ ((features f).order.val-34)%2=0)) := by decide +kernel
theorem matrix_identity : ∀ i j : Fin 38, matrixEntry contributions i j=if i=j then diagonal i else 0 := by decide +kernel
end C34
end ThomsonNine.PairAddition
