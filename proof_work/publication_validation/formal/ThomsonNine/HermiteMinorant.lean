import ThomsonNine.HermiteFactor
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith

noncomputable section
namespace ThomsonNine.HermiteFactor
open Polynomial

/-- Nonnegativity of the algebraic residual suffices for the Coulomb minorant;
no sign premise on H and no analytic remainder formula are needed. -/
theorem minorant_of_G_nonneg (H : ℝ[X]) (t : ℝ) (ht : t < 1)
    (hG : 0 ≤ (G H).eval t) : H.eval t ≤ (Real.sqrt (2-2*t))⁻¹ := by
  have hx : 0 < 2-2*t := by linarith
  have hs : 0 < Real.sqrt (2-2*t) := Real.sqrt_pos.mpr hx
  have hsq := Real.sq_sqrt (le_of_lt hx)
  have hg : (2-2*t)*(H.eval t)^2 ≤ 1 := by
    simpa only [G,eval_sub,eval_one,eval_mul,eval_C,eval_X,eval_pow,sub_nonneg] using hG
  have hprod : Real.sqrt (2-2*t)*H.eval t ≤ 1 := by
    nlinarith [sq_nonneg (Real.sqrt (2-2*t)*H.eval t-1)]
  rw [← one_div, le_div_iff₀ hs]
  simpa only [mul_comm] using hprod

 theorem minorant_of_factor {I : Type*} [Fintype I]
    (H Q : ℝ[X]) (xi : I → ℝ)
    (hfactor : G H = (∏ i, (X-C (xi i))^2)*Q)
    (t : ℝ) (ht : t < 1) (hQ : 0 ≤ Q.eval t) :
    H.eval t ≤ (Real.sqrt (2-2*t))⁻¹ := by
  apply minorant_of_G_nonneg H t ht
  rw [hfactor,eval_mul,eval_prod]
  apply mul_nonneg _ hQ
  apply Finset.prod_nonneg
  intro i hi
  simp only [eval_pow,eval_sub,eval_X,eval_C]
  exact sq_nonneg (t-xi i)
end ThomsonNine.HermiteFactor
