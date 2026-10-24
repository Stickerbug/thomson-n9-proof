import ThomsonCertificate.GenericBernstein
import ThomsonCertificate.GenericCoverage
import ThomsonCertificate.GenericPSD
import ThomsonCertificate.GenericCertificate

open scoped Matrix

/-! A tiny composition example for the generic certificate interfaces. -/
namespace ThomsonCertificate

/-- A one-leaf certificate system for a Bernstein tensor on the unit cube. -/
def unitCubeSpec {d n : ℕ}
    (coeff : (Fin d → Fin (n + 1)) → ℝ)
    (hcoeff : ∀ idx, 0 ≤ coeff idx) :
    Spec Unit (Fin d → ℝ) :=
  { inside := fun _ x => ∀ j, 0 ≤ x j ∧ x j ≤ 1
    domain := fun _ => True
    goal := fun x => 0 ≤ tensor coeff x
    terminal := fun _ => True
    splits := fun _ _ _ => False
    leaf_sound := by
      intro b hb x hdomain hinside
      exact tensor_nonneg coeff hcoeff x hinside
    split_sound := by
      intro b l r hsplit
      exact False.elim hsplit }

/-- The same toy instance packaged as an indexed certificate object. -/
def unitCubeCertificate {d n : ℕ}
    (coeff : (Fin d → Fin (n + 1)) → ℝ)
    (hcoeff : ∀ idx, 0 ≤ coeff idx) : Certificate 0 :=
  { Box := Unit
    Point := Fin d → ℝ
    spec := unitCubeSpec coeff hcoeff
    tree := Tree.leaf ()
    checked := by trivial }

theorem unit_cube_certificate_object_sound {d n : ℕ}
    (coeff : (Fin d → Fin (n + 1)) → ℝ)
    (hcoeff : ∀ idx, 0 ≤ coeff idx)
    (x : Fin d → ℝ)
    (hx : ∀ j, 0 ≤ x j ∧ x j ≤ 1) :
    0 ≤ tensor coeff x := by
  exact (unitCubeCertificate coeff hcoeff).sound x trivial hx

theorem unit_cube_certificate_sound {d n : ℕ}
    (coeff : (Fin d → Fin (n + 1)) → ℝ)
    (hcoeff : ∀ idx, 0 ≤ coeff idx)
    (x : Fin d → ℝ)
    (hx : ∀ j, 0 ≤ x j ∧ x j ≤ 1) :
    0 ≤ tensor coeff x := by
  let S := unitCubeSpec coeff hcoeff
  have hc : Checked S (Tree.leaf ()) := by
    exact trivial
  have hs := sound S (Tree.leaf ()) hc x trivial hx
  exact hs

/-- The three generic certificate ingredients compose into one nonnegative goal.

This is deliberately a small interface test: the vectors in the PSD sum are
supplied by the caller, while the Bernstein tensor is checked on the unit cube.
-/
theorem unit_cube_with_psd_certificate_sound {d n K : ℕ}
    {m : Fin K → ℕ}
    (coeff : (Fin d → Fin (n + 1)) → ℝ)
    (hcoeff : ∀ idx, 0 ≤ coeff idx)
    (A : (k : Fin K) → Matrix (Fin (m k)) (Fin (m k)) ℝ)
    (hA : ∀ k, (A k).PosSemidef)
    (x : Fin d → ℝ)
    (hx : ∀ j, 0 ≤ x j ∧ x j ≤ 1)
    (y : (k : Fin K) → Fin (m k) → ℝ) :
    0 ≤ tensor coeff x + ∑ k : Fin K, y k ⬝ᵥ ((A k) *ᵥ (y k)) := by
  exact add_nonneg (tensor_nonneg coeff hcoeff x hx)
    (finite_psd_sum_nonneg A hA y)

end ThomsonCertificate
