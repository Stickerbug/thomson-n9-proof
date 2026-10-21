/-! A generic coverage lemma. This is not a proof of any Thomson energy statement. -/
namespace ThomsonNine.Coverage
universe u v
inductive Tree (Box : Type u) where
  | leaf : Box → Tree Box
  | split : Box → Tree Box → Tree Box → Tree Box

def root {Box : Type u} : Tree Box → Box
  | .leaf b => b
  | .split b _ _ => b

def Checked {Box : Type u} (terminal : Box → Prop)
    (splits : Box → Box → Box → Prop) : Tree Box → Prop
  | .leaf b => terminal b
  | .split b l r => splits b (root l) (root r) ∧
      Checked terminal splits l ∧ Checked terminal splits r

theorem coverage_sound {Box : Type u} {Point : Type v}
    (inside : Box → Point → Prop) (goal : Point → Prop)
    (terminal : Box → Prop) (splits : Box → Box → Box → Prop)
    (leaf_sound : ∀ b, terminal b → ∀ x, inside b x → goal x)
    (split_sound : ∀ b l r, splits b l r → ∀ x,
      inside b x → inside l x ∨ inside r x)
    (tree : Tree Box) (checked : Checked terminal splits tree) :
    ∀ x, inside (root tree) x → goal x := by
  induction tree with
  | leaf b => exact leaf_sound b checked
  | split b l r ihl ihr =>
    intro x hx
    cases split_sound b (root l) (root r) checked.1 x hx with
    | inl hl => exact ihl checked.2.1 x hl
    | inr hr => exact ihr checked.2.2 x hr
end ThomsonNine.Coverage
