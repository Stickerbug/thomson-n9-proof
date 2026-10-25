import Mathlib

/-!
# Abstract Delsarte/Legendre lower-bound bridge

This interface isolates the obligations needed to turn a polynomial minorant and
nonnegative harmonic sums into a pair-energy lower bound.  It deliberately does
not assert the spherical-harmonic addition theorem or import an external
Fraction certificate: those are instance-specific proof obligations.
-/

namespace ThomsonCertificate

universe u

structure DelsarteBridge (N d : ℕ) where
  Config : Type u
  feasible : Config → Prop
  inner : Config → Fin N → Fin N → ℝ
  potential : ℝ → ℝ
  energy : Config → ℝ
  a0 : ℝ
  coeff : Fin d → ℝ
  coeff_nonneg : ∀ k, 0 ≤ coeff k
  basis : Fin d → ℝ → ℝ
  lowerBound : ℝ
  /-- The polynomial minorant.  In an instance this is checked on the full
  inner-product domain, usually by a Bernstein certificate. -/
  minorant : ∀ t, a0 + ∑ k, coeff k * basis k t ≤ potential t
  /-- Each positive-degree harmonic sum is nonnegative.  For S² this normally
  comes from the addition theorem and a Gram-square identity. -/
  harmonic_nonneg : ∀ (x : Config), feasible x → ∀ k,
    0 ≤ ∑ i, ∑ j, basis k (inner x i j)
  /-- The exact finite-sum identity for the off-diagonal pair energy.  This is
  kept explicit so the bridge cannot silently assume a Thomson-specific
  counting convention. -/
  energy_eq_offdiag : ∀ x, feasible x →
    energy x = (1 / 2 : ℝ) *
      (∑ i, ∑ j, if i = j then 0 else potential (inner x i j))
  /-- The coefficient bookkeeping identity.  It is the only combinatorial
  input beyond the pointwise minorant and harmonic positivity. -/
  offdiag_identity : ∀ x, feasible x →
    lowerBound + (1 / 2 : ℝ) *
        ∑ k, coeff k * (∑ i, ∑ j, basis k (inner x i j)) =
      (1 / 2 : ℝ) *
        (∑ i, ∑ j, if i = j then 0 else
          (a0 + ∑ k, coeff k * basis k (inner x i j)))

namespace DelsarteBridge

/-- The polynomial supplied by the certificate data. -/
def polynomial {N d : ℕ} (D : DelsarteBridge N d) (t : ℝ) : ℝ :=
  D.a0 + ∑ k, D.coeff k * D.basis k t

private theorem offdiag_minorant {N d : ℕ} (D : DelsarteBridge N d)
    (x : D.Config) (i j : Fin N) :
    (if i = j then 0 else D.polynomial (D.inner x i j)) ≤
      (if i = j then 0 else D.potential (D.inner x i j)) := by
  by_cases h : i = j
  · simp [h]
  · simp only [h, ↓reduceIte]
    exact D.minorant _

/-- Soundness of the abstract Delsarte bridge. -/
theorem sound {N d : ℕ} (D : DelsarteBridge N d)
    (x : D.Config) (hx : D.feasible x) :
    D.lowerBound ≤ D.energy x := by
  have hrem : 0 ≤ ∑ k, D.coeff k * (∑ i, ∑ j, D.basis k (D.inner x i j)) := by
    exact Finset.sum_nonneg (fun k hk =>
      mul_nonneg (D.coeff_nonneg k) (D.harmonic_nonneg x hx k))
  have hsum :
      (∑ i, ∑ j, if i = j then 0 else D.polynomial (D.inner x i j)) ≤
        (∑ i, ∑ j, if i = j then 0 else D.potential (D.inner x i j)) := by
    refine Finset.sum_le_sum (fun i hi => ?_)
    refine Finset.sum_le_sum (fun j hj => ?_)
    simpa [polynomial] using offdiag_minorant D x i j
  calc
    D.lowerBound ≤ D.lowerBound + (1 / 2 : ℝ) *
        ∑ k, D.coeff k * (∑ i, ∑ j, D.basis k (D.inner x i j)) := by
          nlinarith
    _ = (1 / 2 : ℝ) *
        (∑ i, ∑ j, if i = j then 0 else
          (D.a0 + ∑ k, D.coeff k * D.basis k (D.inner x i j))) := by
          exact D.offdiag_identity x hx
    _ ≤ (1 / 2 : ℝ) *
        (∑ i, ∑ j, if i = j then 0 else D.potential (D.inner x i j)) := by
          exact mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = D.energy x := by
      symm
      exact D.energy_eq_offdiag x hx

end DelsarteBridge

end ThomsonCertificate
