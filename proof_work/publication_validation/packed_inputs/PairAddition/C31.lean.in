import PairAddition.Metadata
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.PairAddition
namespace C31
def contributions : List Contribution := [⟨131,0,29663930715943426919727490765160448,[(-5),0,1035,0,(-24495),0,119209]⟩,
⟨133,1,(-3216417630485865861724737927250968576),[3,0,(-429),0,5609,0,(-5183)]⟩,
⟨135,2,645882651455141548798866565593426821120,[(-1),0,75,0,(-147),0,73]⟩,
⟨137,3,(-14818393403385104676728281490614906781696),[1,0,(-3),0,3,0,(-1)]⟩]
def diagonal : Fin 38 → ℤ := ![(-14200716912336437335011944379097609666560),
0,
2939548400853642528347472486473205200977920,
0,
(-69569312153536206504223515513199189756477440),
0,
338570652480542871653887775497569390148190208,
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
theorem contributions_valid : contributions.all (fun c => decide (Valid 31 c))=true := by decide +kernel
theorem features_complete : contributions.map Contribution.feature=
    (List.finRange 138).filter (fun f => decide (31≤(features f).order.val ∧ ((features f).order.val-31)%2=0)) := by decide +kernel
theorem matrix_identity : ∀ i j : Fin 38, matrixEntry contributions i j=if i=j then diagonal i else 0 := by decide +kernel
end C31
end ThomsonNine.PairAddition
