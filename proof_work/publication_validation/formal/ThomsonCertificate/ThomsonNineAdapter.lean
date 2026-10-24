import ThomsonCertificate.GenericCertificate
import MainCoverage.Final

/-!
# n=9 adapter for the generic certificate interface

This is a thin instance adapter.  It exposes the already checked n=9 global
residual theorem through `Certificate 9`; it does not alter the frozen root
theorem or claim that candidate discovery is generic.
-/

namespace ThomsonNine

open ThomsonNine.PackedMain
open ThomsonCertificate

def n9CertificateSpec : Spec Unit (Fin 3 → ℝ) :=
  { inside := fun _ _ => True
    domain := fun p => RootCube p ∧ Monotone p ∧ 0 ≤ gramFn p
    goal := fun p => 0 ≤ ActualCoulombGlobal.residual p
    terminal := fun _ => True
    splits := fun _ _ _ => False
    leaf_sound := by
      intro b hb p hp hi
      exact ordered_residual_from_frontier certifiedChunk rootCut root_cut_checked
        p hp.1 hp.2.1 hp.2.2
    split_sound := by
      intro b l r hsplit
      exact False.elim hsplit }

/-- The frozen n=9 frontier is packaged as one checked generic certificate. -/
def n9Certificate : Certificate 9 :=
  { Box := Unit
    Point := Fin 3 → ℝ
    spec := n9CertificateSpec
    tree := Tree.leaf ()
    checked := by trivial }

theorem n9_certificate_sound (p : Fin 3 → ℝ)
    (hp : RootCube p) (ho : Monotone p) (hg : 0 ≤ gramFn p) :
    0 ≤ ActualCoulombGlobal.residual p := by
  exact n9Certificate.sound p ⟨hp, ho, hg⟩ trivial

end ThomsonNine
