import PairAddition.C00
import PairAddition.C01
import PairAddition.C02
import PairAddition.C03
import PairAddition.C04
import PairAddition.C05
import PairAddition.C06
import PairAddition.C07
import PairAddition.C08
import PairAddition.C09
import PairAddition.C10
import PairAddition.C11
import PairAddition.C12
import PairAddition.C13
import PairAddition.C14
import PairAddition.C15
import PairAddition.C16
import PairAddition.C17
import PairAddition.C18
import PairAddition.C19
import PairAddition.C20
import PairAddition.C21
import PairAddition.C22
import PairAddition.C23
import PairAddition.C24
import PairAddition.C25
import PairAddition.C26
import PairAddition.C27
import PairAddition.C28
import PairAddition.C29
import PairAddition.C30
import PairAddition.C31
import PairAddition.C32
import PairAddition.C33
import PairAddition.C34
import PairAddition.C35
import PairAddition.C36
import PairAddition.C37
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Taylor
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.PairAddition
open Polynomial
open scoped BigOperators
def pCoefficient : Fin 38 → ℚ := ![(92497259316771141/131072000000000000 : ℚ),
(6085817050462522671881/17179869184000000000000 : ℚ),
(38886225988266831/131072000000000000 : ℚ),
(82753086447031895131/343597383680000000000 : ℚ),
(-316418983121241/5242880000000000 : ℚ),
(-14931511050657469192911/17179869184000000000000 : ℚ),
(59106730861098921/26214400000000000 : ℚ),
(14308484040627300208113/1073741824000000000000 : ℚ),
(-285521133916033587/13107200000000000 : ℚ),
(313797382771584171317/6871947673600000000 : ℚ),
(7141684265675490531/65536000000000000 : ℚ),
(-50851602635594097025143/17179869184000000000 : ℚ),
(-21588886194189106793/65536000000000000 : ℚ),
(1214986769507396103125229/34359738368000000000 : ℚ),
(332467978208161257/524288000000000 : ℚ),
(-10318882484359215761124177/42949672960000000000 : ℚ),
(-4100438397900655503/5242880000000000 : ℚ),
(378840330751993635598167303/343597383680000000000 : ℚ),
(3135629363100501267/5242880000000000 : ℚ),
(-125622872218291040194340739/34359738368000000000 : ℚ),
(-6766358099322134313/26214400000000000 : ℚ),
(3109230575699139461046701367/343597383680000000000 : ℚ),
(1259538520653037989/26214400000000000 : ℚ),
(-728834074227583565066918001/42949672960000000000 : ℚ),
(0/1 : ℚ),
(103921456053279978841225197609/4294967296000000000000 : ℚ),
(0/1 : ℚ),
(-55984452729256882686818489051/2147483648000000000000 : ℚ),
(0/1 : ℚ),
(3585490572425940877194869373/171798691840000000000 : ℚ),
(0/1 : ℚ),
(-2583095358629441277118884387/214748364800000000000 : ℚ),
(0/1 : ℚ),
(16203052704130131647382092973/3435973836800000000000 : ℚ),
(0/1 : ℚ),
(-9667367579775120562723769757/8589934592000000000000 : ℚ),
(0/1 : ℚ),
(2119272772743494898134640217/17179869184000000000000 : ℚ)]
def P : ℝ[X] := ofFn 38 (fun i => (pCoefficient i : ℝ))
def contributions : Fin 38 → List Contribution := ![C00.contributions,C01.contributions,C02.contributions,C03.contributions,C04.contributions,C05.contributions,C06.contributions,C07.contributions,C08.contributions,C09.contributions,C10.contributions,C11.contributions,C12.contributions,C13.contributions,C14.contributions,C15.contributions,C16.contributions,C17.contributions,C18.contributions,C19.contributions,C20.contributions,C21.contributions,C22.contributions,C23.contributions,C24.contributions,C25.contributions,C26.contributions,C27.contributions,C28.contributions,C29.contributions,C30.contributions,C31.contributions,C32.contributions,C33.contributions,C34.contributions,C35.contributions,C36.contributions,C37.contributions]
def diagonal : Fin 38 → Fin 38 → ℤ := ![C00.diagonal,C01.diagonal,C02.diagonal,C03.diagonal,C04.diagonal,C05.diagonal,C06.diagonal,C07.diagonal,C08.diagonal,C09.diagonal,C10.diagonal,C11.diagonal,C12.diagonal,C13.diagonal,C14.diagonal,C15.diagonal,C16.diagonal,C17.diagonal,C18.diagonal,C19.diagonal,C20.diagonal,C21.diagonal,C22.diagonal,C23.diagonal,C24.diagonal,C25.diagonal,C26.diagonal,C27.diagonal,C28.diagonal,C29.diagonal,C30.diagonal,C31.diagonal,C32.diagonal,C33.diagonal,C34.diagonal,C35.diagonal,C36.diagonal,C37.diagonal]
theorem coefficient_lengths : ∀ h, (contributions h).all (fun c => decide (c.coefficients.length≤38))=true := by decide +kernel
theorem diagonal_relation : ∀ h i : Fin 38, ((diagonal h i : ℤ) : ℚ)=
    (denominator h : ℚ)*(i.val+h.val).choose h.val*(if hi : i.val+h.val<38 then pCoefficient ⟨i.val+h.val,hi⟩ else 0) := by decide +kernel
theorem qCoefficient_nonzero_iff : ∀ m h : Fin 38, qCoefficient m h≠0 ↔ h.val≤m.val ∧ (m.val-h.val)%2=0 := by decide +kernel
theorem all_valid (h : Fin 38) : (contributions h).all (fun c => decide (Valid h c))=true := by
  fin_cases h
  · exact C00.contributions_valid
  · exact C01.contributions_valid
  · exact C02.contributions_valid
  · exact C03.contributions_valid
  · exact C04.contributions_valid
  · exact C05.contributions_valid
  · exact C06.contributions_valid
  · exact C07.contributions_valid
  · exact C08.contributions_valid
  · exact C09.contributions_valid
  · exact C10.contributions_valid
  · exact C11.contributions_valid
  · exact C12.contributions_valid
  · exact C13.contributions_valid
  · exact C14.contributions_valid
  · exact C15.contributions_valid
  · exact C16.contributions_valid
  · exact C17.contributions_valid
  · exact C18.contributions_valid
  · exact C19.contributions_valid
  · exact C20.contributions_valid
  · exact C21.contributions_valid
  · exact C22.contributions_valid
  · exact C23.contributions_valid
  · exact C24.contributions_valid
  · exact C25.contributions_valid
  · exact C26.contributions_valid
  · exact C27.contributions_valid
  · exact C28.contributions_valid
  · exact C29.contributions_valid
  · exact C30.contributions_valid
  · exact C31.contributions_valid
  · exact C32.contributions_valid
  · exact C33.contributions_valid
  · exact C34.contributions_valid
  · exact C35.contributions_valid
  · exact C36.contributions_valid
  · exact C37.contributions_valid
theorem all_complete (h : Fin 38) : (contributions h).map Contribution.feature=
    (List.finRange 138).filter (fun f => decide (h.val≤(features f).order.val ∧ ((features f).order.val-h.val)%2=0)) := by
  fin_cases h
  · exact C00.features_complete
  · exact C01.features_complete
  · exact C02.features_complete
  · exact C03.features_complete
  · exact C04.features_complete
  · exact C05.features_complete
  · exact C06.features_complete
  · exact C07.features_complete
  · exact C08.features_complete
  · exact C09.features_complete
  · exact C10.features_complete
  · exact C11.features_complete
  · exact C12.features_complete
  · exact C13.features_complete
  · exact C14.features_complete
  · exact C15.features_complete
  · exact C16.features_complete
  · exact C17.features_complete
  · exact C18.features_complete
  · exact C19.features_complete
  · exact C20.features_complete
  · exact C21.features_complete
  · exact C22.features_complete
  · exact C23.features_complete
  · exact C24.features_complete
  · exact C25.features_complete
  · exact C26.features_complete
  · exact C27.features_complete
  · exact C28.features_complete
  · exact C29.features_complete
  · exact C30.features_complete
  · exact C31.features_complete
  · exact C32.features_complete
  · exact C33.features_complete
  · exact C34.features_complete
  · exact C35.features_complete
  · exact C36.features_complete
  · exact C37.features_complete
theorem all_matrices (h : Fin 38) : ∀ i j : Fin 38,
    matrixEntry (contributions h) i j=if i=j then diagonal h i else 0 := by
  fin_cases h
  · exact C00.matrix_identity
  · exact C01.matrix_identity
  · exact C02.matrix_identity
  · exact C03.matrix_identity
  · exact C04.matrix_identity
  · exact C05.matrix_identity
  · exact C06.matrix_identity
  · exact C07.matrix_identity
  · exact C08.matrix_identity
  · exact C09.matrix_identity
  · exact C10.matrix_identity
  · exact C11.matrix_identity
  · exact C12.matrix_identity
  · exact C13.matrix_identity
  · exact C14.matrix_identity
  · exact C15.matrix_identity
  · exact C16.matrix_identity
  · exact C17.matrix_identity
  · exact C18.matrix_identity
  · exact C19.matrix_identity
  · exact C20.matrix_identity
  · exact C21.matrix_identity
  · exact C22.matrix_identity
  · exact C23.matrix_identity
  · exact C24.matrix_identity
  · exact C25.matrix_identity
  · exact C26.matrix_identity
  · exact C27.matrix_identity
  · exact C28.matrix_identity
  · exact C29.matrix_identity
  · exact C30.matrix_identity
  · exact C31.matrix_identity
  · exact C32.matrix_identity
  · exact C33.matrix_identity
  · exact C34.matrix_identity
  · exact C35.matrix_identity
  · exact C36.matrix_identity
  · exact C37.matrix_identity
end ThomsonNine.PairAddition
