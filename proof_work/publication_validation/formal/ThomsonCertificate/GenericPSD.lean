import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Generic PSD block certificates

The statements here are independent of the Thomson particle count.  They cover
both a direct PSD quadratic form and a congruence-reduced block `N * B * Nᵀ`.
-/

open scoped Matrix

namespace ThomsonCertificate

/-- A positive-semidefinite real matrix has a nonnegative quadratic form. -/
theorem psd_quadratic_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (x : Fin n → ℝ) :
    0 ≤ x ⬝ᵥ (A *ᵥ x) := by
  simpa using hA.dotProduct_mulVec_nonneg x

/-- Congruence by an arbitrary rectangular matrix preserves nonnegative quadratic forms. -/
theorem reduced_psd_quadratic_nonneg {m n : ℕ}
    {B : Matrix (Fin m) (Fin m) ℝ} (hB : B.PosSemidef)
    (N : Matrix (Fin n) (Fin m) ℝ) (x : Fin n → ℝ) :
    0 ≤ x ⬝ᵥ ((N * B * N.transpose) *ᵥ x) := by
  have hN : (N * B * N.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hB.mul_mul_conjTranspose_same N
  exact psd_quadratic_nonneg hN x

/-- A finite family of PSD quadratic forms can be summed without further assumptions. -/
theorem finite_psd_sum_nonneg {K : ℕ} {m : Fin K → ℕ}
    (A : (k : Fin K) → Matrix (Fin (m k)) (Fin (m k)) ℝ)
    (hA : ∀ k, (A k).PosSemidef)
    (x : (k : Fin K) → Fin (m k) → ℝ) :
    0 ≤ ∑ k : Fin K, x k ⬝ᵥ ((A k) *ᵥ (x k)) := by
  apply Finset.sum_nonneg
  intro k hk
  exact psd_quadratic_nonneg (hA k) (x k)

end ThomsonCertificate
