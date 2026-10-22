import PairAddition.Metadata
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.PairAddition
namespace C29
def contributions : List Contribution := [⟨129,0,134404803350489940734372959223808,[35,0,(-9380),0,323610,0,(-3063508),0,7987003]⟩,
⟨131,1,(-229895463048561558627888053429993472),[(-5),0,1040,0,(-25530),0,143704,0,(-119209)]⟩,
⟨133,2,12061566114321996981467767227191132160,[3,0,(-432),0,6038,0,(-10792),0,5183]⟩,
⟨135,3,(-1564247046492920938497254963546580582400),[(-1),0,76,0,(-222),0,220,0,(-73)]⟩,
⟨137,4,26100579290053309373782768534605801717760,[1,0,(-4),0,6,0,(-4),0,1]⟩]
def diagonal : Fin 38 → ℤ := ![24639303597897176719330425881643240652800,
0,
(-6603333364236443360780554136280388494950400),
0,
227815001066157295946929117701673403075788800,
0,
(-2156648676759622401630928980909174882450800640),
0,
5622691192980444118537779128798920229246730240,
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
theorem contributions_valid : contributions.all (fun c => decide (Valid 29 c))=true := by decide +kernel
theorem features_complete : contributions.map Contribution.feature=
    (List.finRange 138).filter (fun f => decide (29≤(features f).order.val ∧ ((features f).order.val-29)%2=0)) := by decide +kernel
theorem matrix_identity : ∀ i j : Fin 38, matrixEntry contributions i j=if i=j then diagonal i else 0 := by decide +kernel
end C29
end ThomsonNine.PairAddition
