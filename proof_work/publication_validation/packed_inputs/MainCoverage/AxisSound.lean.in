import MainCoverage.AxisCertificate
import PackedTensor.Linear
import PackedRadix.Univariate

noncomputable section
namespace ThomsonNine.PackedMain
open scoped BigOperators
open ThomsonNine.PackedTensor ThomsonNine.PackedRadix ThomsonNine.MainAxis

theorem diagonal_scaled_identity (word : ℕ) (w : AxisWitness)
    (h : integerCombination 20 (upperCoefficients word)=List.ofFn w.ad) (t : ℝ) :
    uniValue 20 offset scale word t= -powers 21 (fun i => (w.ad i : ℝ)) t/(scale : ℝ) := by
  have he : (fun i : Fin 21 => decode offset scale word i.val)=
      fun i => -(upperCoefficients word i : ℝ)/(scale : ℝ) := by
    funext i
    simp [decode,upperCoefficients]
  rw [uniValue,he,curve_div,curve_neg,diagonal_identity word w h t]

theorem h_curve_lower (e : AxisEntry) (w : AxisWitness)
    (h : ∀ i : Fin 11, (hCoefficients e i : ℚ)≤w.bern i)
    (hq : exactCombination 10 w.bern=ThomsonNine.ExactPolynomial.trim
      ((List.ofFn (witnessQ w)).map (fun z : ℤ => (z : ℚ))))
    (t : ℝ) (ht : 0≤t ∧ t≤1) :
    axisCurve e t≤powers 11 (fun i => (witnessQ w i : ℝ)) t/(scale : ℝ) := by
  have hc (i : Fin 11) : (hCoefficients e i : ℝ)≤(w.bern i : ℝ) := by exact_mod_cast h i
  have hp := curve_mono 10 (fun i => (hCoefficients e i : ℝ)) (fun i => (w.bern i : ℝ)) hc t ht
  have hh := div_le_div_of_nonneg_right hp (le_of_lt scale_pos)
  rw [q_identity w hq t,← curve_div] at hh
  simpa only [axisCurve,axisValues,hCoefficients,Int.cast_sub,Int.cast_natCast] using hh

attribute [local irreducible] uniValue

theorem axisCertificateOK_sound (e : AxisEntry) (word : ℕ) (w : AxisWitness)
    (h : axisCertificateOK e word w=true) (D : ℝ → ℝ)
    (hD : ∀ t, 0≤t ∧ t≤1 → uniValue 20 offset scale word t≤-D (qPoint e t))
    (t : ℝ) (ht : 0≤t ∧ t≤1) : axisCurve e t≤ThomsonNine.ActualCoulombGlobal.coulomb (qPoint e t)-D (qPoint e t) := by
  have hp : leftQ e<rightQ e ∧ rightQ e<1 ∧ 0≤lambdaQ e ∧
      (2-2*leftQ e)*(w.num : ℚ)^2≤(scale : ℚ)^2 ∧
      (∀ k : Fin 11, (w.af k : ℚ)≤(w.num : ℚ)*taylorCoefficient k*(lambdaQ e)^k.val) ∧
      integerCombination 20 (upperCoefficients word)=List.ofFn w.ad ∧
      exactCombination 10 w.bern=ThomsonNine.ExactPolynomial.trim
        ((List.ofFn (witnessQ w)).map (fun z : ℤ => (z : ℚ))) ∧
      (∀ i : Fin 11, (hCoefficients e i : ℚ)≤w.bern i) := of_decide_eq_true h
  have hlr : (leftQ e : ℝ)<(rightQ e : ℝ) := by exact_mod_cast hp.1
  have hr : (rightQ e : ℝ)<1 := by exact_mod_cast hp.2.1
  have hlam : (0:ℝ)≤(lambdaQ e : ℝ) := by exact_mod_cast hp.2.2.1
  have hnSquare : (2-2*(leftQ e : ℝ))*(w.num : ℝ)^2≤(scale : ℝ)^2 := by
    exact_mod_cast hp.2.2.2.1
  have hAF (k : Fin 11) : (w.af k : ℝ)≤(w.num : ℝ)*(taylorCoefficient k : ℝ)*(lambdaQ e : ℝ)^k.val := by
    exact_mod_cast hp.2.2.2.2.1 k
  have hdpoly := hp.2.2.2.2.2.1
  have hqpoly := hp.2.2.2.2.2.2.1
  have hhCoeffs := hp.2.2.2.2.2.2.2
  have hN := scaled_square_minorant (2-2*(leftQ e : ℝ)) (w.num : ℝ) (scale : ℝ)
    (by linarith) scale_pos hnSquare
  have hAFpoly := finite_taylor_lower (fun k => (w.af k : ℝ)) (w.num : ℝ) (lambdaQ e : ℝ) t ht.1 hAF
  have hTpos := ThomsonNine.MainCoulombTaylor.T_nonnegative ((lambdaQ e : ℝ)*t) (mul_nonneg hlam ht.1)
  have hNT := mul_le_mul_of_nonneg_right hN hTpos
  have hAffine := ThomsonNine.MainCoulombTaylor.affine_lower (leftQ e : ℝ) (rightQ e : ℝ) t hlr hr ht
  have hlambda : (lambdaQ e : ℝ)=((rightQ e : ℝ)-(leftQ e : ℝ))/(1-(leftQ e : ℝ)) := by
    simp only [lambdaQ,Rat.cast_div,Rat.cast_sub,Rat.cast_one]
  rw [← hlambda] at hAffine
  have hAFscaled : powers 11 (fun k => (w.af k : ℝ)) t/(scale : ℝ)≤
      ThomsonNine.ActualCoulombGlobal.coulomb (qPoint e t) := by
    have he : (w.num : ℝ)*ThomsonNine.MainCoulombTaylor.T.eval ((lambdaQ e : ℝ)*t)/(scale : ℝ)=
        ((w.num : ℝ)/(scale : ℝ))*ThomsonNine.MainCoulombTaylor.T.eval ((lambdaQ e : ℝ)*t) := by ring
    have hh := div_le_div_of_nonneg_right hAFpoly (le_of_lt scale_pos)
    rw [he] at hh
    exact (hh.trans hNT).trans hAffine
  have hDpoly := hD t ht
  rw [diagonal_scaled_identity word w hdpoly t] at hDpoly
  have hQpoly := truncate_lower (fun i => (w.af i : ℝ)) (fun i => (w.ad i : ℝ)) t ht
  rw [← witnessQ_cast w] at hQpoly
  have hQscaled := div_le_div_of_nonneg_right hQpoly (le_of_lt scale_pos)
  rw [sub_div] at hQscaled
  have hH := h_curve_lower e w hhCoeffs hqpoly t ht
  have heNeg : -powers 21 (fun i => (w.ad i : ℝ)) t/(scale : ℝ)=
      -(powers 21 (fun i => (w.ad i : ℝ)) t/(scale : ℝ)) := by ring
  rw [heNeg] at hDpoly
  linarith only [hDpoly,hQscaled,hH,hAFscaled]
end ThomsonNine.PackedMain
