import PairAddition.Metadata
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.PairAddition
namespace C28
def contributions : List Contribution := [⟨128,0,246408806142564891346350425243648,[0,315,0,(-28140),0,582498,0,(-3938796),0,7987003]⟩,
⟨130,1,(-540307309468969561752179296079708160),[0,(-35),0,2450,0,(-36708),0,153502,0,(-119209)]⟩,
⟨132,2,39571683575068531510916472680724037632,[0,15,0,(-740),0,6618,0,(-11076),0,5183]⟩,
⟨134,3,(-8529111084840663845299318308148913111040),[0,(-3),0,82,0,(-228),0,222,0,(-73)]⟩,
⟨136,4,425765699668994609159831411720757140520960,[0,1,0,(-4),0,6,0,(-4),0,1]⟩]
def diagonal : Fin 38 → ℤ := ![0,
357269902169509062430291175283826989465600,
0,
(-31916111260476142910439344992021877725593600),
0,
660663503091856158246094441334852868919787520,
0,
(-4467343687573503546235495746169005113648087040),
0,
9058780255357382190977533040842704813786398720,
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
theorem contributions_valid : contributions.all (fun c => decide (Valid 28 c))=true := by decide +kernel
theorem features_complete : contributions.map Contribution.feature=
    (List.finRange 138).filter (fun f => decide (28≤(features f).order.val ∧ ((features f).order.val-28)%2=0)) := by decide +kernel
theorem matrix_identity : ∀ i j : Fin 38, matrixEntry contributions i j=if i=j then diagonal i else 0 := by decide +kernel
end C28
end ThomsonNine.PairAddition
