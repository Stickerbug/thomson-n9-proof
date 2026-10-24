import Mathlib
import ThomsonCertificate.GenericCertificate

/-!
# Generic reduction-to-lower-bound bridge

An instance-specific Thomson development usually has two logically separate
parts: a certificate proves a reduced goal, and a reduction theorem transfers
that goal back to the original configuration energy.  This file packages the
second interface without mentioning spheres, particle counts, or a particular
residual formula.
-/

namespace ThomsonCertificate

universe u v

/-- The non-certificate obligations needed to turn a checked goal into an
energy lower bound for one indexed instance. -/
structure LowerBoundBridge {n : ℕ} (C : Certificate n) where
  Config : Type u
  feasible : Config → Prop
  energy : Config → ℝ
  lowerBound : ℝ
  reduce : Config → C.Point
  admissible : ∀ (x : Config), feasible x →
    C.spec.domain (reduce x) ∧
      C.spec.inside (Tree.root C.tree) (reduce x)
  conclude : ∀ (x : Config), feasible x → C.spec.goal (reduce x) →
    (lowerBound : ℝ) ≤ (energy x : ℝ)

namespace LowerBoundBridge

/-- Soundness of the reduction bridge and its checked certificate. -/
theorem sound {n : ℕ} {C : Certificate n} (B : LowerBoundBridge C) :
    ∀ x, B.feasible x → B.lowerBound ≤ B.energy x := by
  intro x hx
  have ha := B.admissible x hx
  have hg := C.sound (B.reduce x) ha.1 ha.2
  exact B.conclude x hx hg

end LowerBoundBridge

end ThomsonCertificate
