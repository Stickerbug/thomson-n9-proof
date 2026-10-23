import ThomsonCertificate.GenericBernstein
import ThomsonCertificate.GenericCoverage

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

end ThomsonCertificate
