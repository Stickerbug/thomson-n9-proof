import ThomsonNine.CoverageSoundness

/-! Domain-aware coverage.

The generic `Coverage.coverage_sound` lemma requires every leaf to establish the goal
on the *whole* ambient box.  The published certificate instead has leaves that only
exclude the feasible domain `D` (order pruning, negative Gram) or that prove the
residual inequality on `D` (interior sign, local box, boundary multiplier).
This module records the logically correct interface: leaves must be sound only on
`D`, while the split relation only has to cover the ambient box. -/
namespace ThomsonNine.Coverage

universe u v

theorem coverage_sound_on_domain {Box : Type u} {Point : Type v}
    (inside : Box → Point → Prop) (D : Point → Prop) (goal : Point → Prop)
    (terminal : Box → Prop) (splits : Box → Box → Box → Prop)
    (leaf_sound : ∀ b, terminal b → ∀ x, D x → inside b x → goal x)
    (split_sound : ∀ b l r, splits b l r → ∀ x,
      inside b x → inside l x ∨ inside r x)
    (tree : Tree Box) (checked : Checked terminal splits tree) :
    ∀ x, D x → inside (root tree) x → goal x := by
  induction tree with
  | leaf b => exact leaf_sound b checked
  | split b l r ihl ihr =>
    intro x hD hx
    cases split_sound b (root l) (root r) checked.1 x hx with
    | inl hl => exact ihl checked.2.1 x hD hl
    | inr hr => exact ihr checked.2.2 x hD hr

/-- The goal is only claimed on the domain; outside `D` the statement is vacuous. -/
theorem coverage_sound_restricted {Box : Type u} {Point : Type v}
    (inside : Box → Point → Prop) (D : Point → Prop) (goal : Point → Prop)
    (terminal : Box → Prop) (splits : Box → Box → Box → Prop)
    (leaf_sound : ∀ b, terminal b → ∀ x, inside b x → D x → goal x)
    (split_sound : ∀ b l r, splits b l r → ∀ x,
      inside b x → inside l x ∨ inside r x)
    (tree : Tree Box) (checked : Checked terminal splits tree) :
    ∀ x, inside (root tree) x → D x → goal x := by
  induction tree with
  | leaf b => exact leaf_sound b checked
  | split b l r ihl ihr =>
    intro x hx hD
    cases split_sound b (root l) (root r) checked.1 x hx with
    | inl hl => exact ihl checked.2.1 x hl hD
    | inr hr => exact ihr checked.2.2 x hr hD

end ThomsonNine.Coverage
