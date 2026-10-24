import ThomsonCertificate.GenericCoverage

/-!
# Indexed certificate objects

`Spec` and `Checked` describe the soundness kernel.  This file adds the
smallest reusable object that an instance-specific generator can emit: a
certificate indexed by a natural-number problem instance, carrying its point
and box types, the semantic specification, a finite tree, and a checked-tree
proof.  The index is intentionally abstract; instance adapters decide how it
controls their geometry and objective.
-/

namespace ThomsonCertificate

universe u v

/-- A checked finite certificate for an indexed problem instance. -/
structure Certificate (n : ℕ) where
  Box : Type u
  Point : Type v
  spec : Spec Box Point
  tree : Tree Box
  checked : Checked spec tree

namespace Certificate

/-- Every checked certificate proves its goal on the covered domain. -/
theorem sound {n : ℕ} (C : Certificate n) :
    ∀ x, C.spec.domain x →
      C.spec.inside (Tree.root C.tree) x → C.spec.goal x := by
  exact ThomsonCertificate.sound C.spec C.tree C.checked

end Certificate

end ThomsonCertificate
