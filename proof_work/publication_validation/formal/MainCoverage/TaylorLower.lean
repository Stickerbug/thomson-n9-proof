import MainCoverage.TaylorData

noncomputable section
namespace ThomsonNine.MainCoulombTaylor
open Polynomial ThomsonNine.RationalListPolynomial
open scoped BigOperators

theorem eval_nonnegative (l : List ℚ) (hl : ∀ c∈l, 0≤c) (z : ℝ) (hz : 0≤z) :
    0≤(realPolynomial l).eval z := by
  induction l with
  | nil => simp
  | cons c l ih =>
    rw [cons,eval_add,eval_C,eval_mul,eval_X]
    exact add_nonneg (by exact_mod_cast hl c (by simp))
      (mul_nonneg hz (ih (fun a ha => hl a (by simp [ha]))))

theorem remainder_polynomial : realPolynomial remainderCoefficients=1-(1-X)*T^2 := by
  rw [← remainder_fields,ExactPolynomial.sub_sound,ExactPolynomial.mul_sound,ExactPolynomial.pow_sound]
  have h1 : realPolynomial [1]=(1 : ℝ[X]) := by simp
  have h2 : realPolynomial [1,-1]=(1 : ℝ[X])-X := by simp;ring
  rw [h1,h2]
  rfl

theorem square_minorant (d y : ℝ) (hd : 0<d) (hy : d*y^2≤1) : y≤(Real.sqrt d)⁻¹ := by
  have hs := Real.sqrt_pos.mpr hd
  have hsq := Real.sq_sqrt (le_of_lt hd)
  have hp : (Real.sqrt d*y)^2≤1 := by rw [mul_pow,hsq];exact hy
  have hm : Real.sqrt d*y≤1 := by nlinarith [sq_nonneg (Real.sqrt d*y-1)]
  rw [← one_div,le_div_iff₀ hs]
  simpa only [mul_comm] using hm

theorem T_nonnegative (z : ℝ) (hz : 0≤z) : 0≤T.eval z :=
  eval_nonnegative coefficients coefficients_nonnegative z hz

theorem T_lower_inverse_sqrt (z : ℝ) (hz : 0≤z) (hz1 : z<1) :
    T.eval z≤(Real.sqrt (1-z))⁻¹ := by
  have h := eval_nonnegative remainderCoefficients remainder_nonnegative z hz
  rw [remainder_polynomial] at h
  simp only [eval_sub,eval_one,eval_mul,eval_X,eval_pow] at h
  apply square_minorant (1-z) (T.eval z) (by linarith)
  linarith

theorem affine_lower (l r s : ℝ) (hlr : l<r) (hr : r<1) (hs : 0≤s ∧ s≤1) :
    (Real.sqrt (2-2*l))⁻¹*T.eval (((r-l)/(1-l))*s)≤
      ActualCoulombGlobal.coulomb (l+(r-l)*s) := by
  let a := (r-l)/(1-l)
  have hl : l<1 := hlr.trans hr
  have hden : 0<1-l := by linarith
  have ha : 0<a := div_pos (sub_pos.mpr hlr) hden
  have ha1 : a<1 := (div_lt_one hden).mpr (by linarith)
  have hz : 0≤a*s := mul_nonneg (le_of_lt ha) hs.1
  have hz1 : a*s<1 := (mul_le_of_le_one_right (le_of_lt ha) hs.2).trans_lt ha1
  have hd : 0<2-2*l := by linarith
  have he : 2-2*(l+(r-l)*s)=(2-2*l)*(1-a*s) := by
    dsimp only [a]
    field_simp
    ring
  have h := mul_le_mul_of_nonneg_left (T_lower_inverse_sqrt (a*s) hz hz1)
    (inv_nonneg.mpr (Real.sqrt_nonneg (2-2*l)))
  unfold ActualCoulombGlobal.coulomb
  rw [he,Real.sqrt_mul (le_of_lt hd),mul_inv_rev]
  simpa only [mul_comm] using h
end ThomsonNine.MainCoulombTaylor
