import PairAddition.Metadata
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.PairAddition
namespace C32
def contributions : List Contribution := [⟨132,0,1364540812933397638307464575197380608,[0,15,0,(-710),0,5183]⟩,
⟨134,1,(-941143292120349113964062709864707653632),[0,(-3),0,76,0,(-73)]⟩,
⟨136,2,100024155472849456567915900061650620776448,[0,1,0,(-2),0,1]⟩]
def diagonal : Fin 38 → ℤ := ![0,
91860887526676329010858515202287662530560,
0,
(-4348082009596012906513969719574949359779840),
0,
31740998670050894217551978952897130326392832,
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
theorem contributions_valid : contributions.all (fun c => decide (Valid 32 c))=true := by decide +kernel
theorem features_complete : contributions.map Contribution.feature=
    (List.finRange 138).filter (fun f => decide (32≤(features f).order.val ∧ ((features f).order.val-32)%2=0)) := by decide +kernel
theorem matrix_identity : ∀ i j : Fin 38, matrixEntry contributions i j=if i=j then diagonal i else 0 := by decide +kernel
end C32
end ThomsonNine.PairAddition
