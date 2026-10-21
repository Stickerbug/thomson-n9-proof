import ThomsonNine.ReducedPSD
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # PSD certificate semantics

The sharp certificate decomposes the quadratic part of the residual into blocks
`A_k = N_k B_k N_kᵀ` and proves each `B_k` positive semidefinite.  This module
records the logical interface: a PSD block contributes a nonnegative quadratic
form, and a finite block-diagonal assembly of PSD blocks has nonnegative total
quadratic form.

The numeric PSD data (the matrices `B_k` and their witnesses) stay outside Lean;
this is the same trust boundary as the Bernstein leaf certificates in
`TreeSemantics`. -/

open scoped BigOperators Matrix

namespace ThomsonNine.PSDSemantics

open ThomsonNine.Semantics

/-- A real positive semidefinite matrix has a nonnegative quadratic form. -/
theorem dotProduct_mulVec_nonneg_real {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (x : Fin n → ℝ) : 0 ≤ x ⬝ᵥ (A *ᵥ x) := by
  simpa using hA.dotProduct_mulVec_nonneg x

/-- The reduced block `N B Nᵀ` has a nonnegative quadratic form whenever `B` is PSD. -/
theorem reduced_quadform_nonneg {m n : ℕ} {B : Matrix (Fin m) (Fin m) ℝ}
    (hB : B.PosSemidef) (N : Matrix (Fin n) (Fin m) ℝ) (x : Fin n → ℝ) :
    0 ≤ x ⬝ᵥ ((N * B * N.transpose) *ᵥ x) :=
  dotProduct_mulVec_nonneg_real (reduced_matrix_psd hB N) x

/-- A finite block assembly of PSD quadratic forms is nonnegative. -/
theorem sum_quadform_nonneg {K : ℕ} (m : ℕ → ℕ)
    (A : (k : ℕ) → Matrix (Fin (m k)) (Fin (m k)) ℝ)
    (hA : ∀ k, (A k).PosSemidef)
    (x : (k : Fin K) → Fin (m k) → ℝ) :
    0 ≤ ∑ k : Fin K, x k ⬝ᵥ ((A k) *ᵥ x k) :=
  Finset.sum_nonneg (fun k _ => dotProduct_mulVec_nonneg_real (hA k) (x k))

/-- The concrete decomposition shape used by the certificate: each summand is a
reduced block `N_k B_k N_kᵀ` with `B_k` PSD, hence the total form is nonnegative. -/
theorem reduced_sum_quadform_nonneg {K : ℕ} (m : ℕ → ℕ)
    (B : (k : ℕ) → Matrix (Fin (m k)) (Fin (m k)) ℝ)
    (hB : ∀ k, (B k).PosSemidef)
    (n : ℕ) (N : (k : ℕ) → Matrix (Fin n) (Fin (m k)) ℝ)
    (x : Fin n → ℝ) :
    0 ≤ ∑ k : Fin K, x ⬝ᵥ (((N k) * (B k) * (N k).transpose) *ᵥ x) :=
  Finset.sum_nonneg (fun k _ => reduced_quadform_nonneg (hB k) (N k) x)

end ThomsonNine.PSDSemantics
