import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Generic finite-dimensional Bernstein certificates

This module is an n-independent kernel component.  It generalizes the current
three-variable Bernstein tensor to any finite coordinate dimension `d`.  A
problem-specific certificate only has to provide a coefficient function and a
box whose normalized coordinates lie in `[0,1]`.
-/

open scoped BigOperators

namespace ThomsonCertificate

/-- The one-dimensional Bernstein basis, with real evaluation. -/
noncomputable def bernstein (n i : ℕ) (z : ℝ) : ℝ :=
  (n.choose i : ℝ) * z ^ i * (1 - z) ^ (n - i)

theorem bernstein_nonneg (n i : ℕ) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ bernstein n i z := by
  unfold bernstein
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz0 _))
    (pow_nonneg (sub_nonneg.mpr hz1) _)

/-- A tensor Bernstein polynomial over an arbitrary finite coordinate set. -/
noncomputable def tensor {d n : ℕ}
    (coeff : (Fin d → Fin (n + 1)) → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ idx : Fin d → Fin (n + 1),
    coeff idx * ∏ j : Fin d, bernstein n (idx j).val (x j)

/-- Nonnegative Bernstein coefficients give a nonnegative tensor on the unit cube. -/
theorem tensor_nonneg {d n : ℕ}
    (coeff : (Fin d → Fin (n + 1)) → ℝ)
    (hcoeff : ∀ idx, 0 ≤ coeff idx)
    (x : Fin d → ℝ)
    (hx : ∀ j, 0 ≤ x j ∧ x j ≤ 1) :
    0 ≤ tensor coeff x := by
  unfold tensor
  apply Finset.sum_nonneg
  intro idx hidx
  apply mul_nonneg
  · exact hcoeff idx
  · apply Finset.prod_nonneg
    intro j hj
    exact bernstein_nonneg n (idx j).val (hx j).1 (hx j).2

end ThomsonCertificate
