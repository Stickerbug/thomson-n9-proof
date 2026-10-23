import Mathlib.Data.Finset.Basic

/-!
# Generic finite certificate-tree soundness

`Spec` packages the domain predicate, target predicate, terminal certificate
predicate and split relation.  The theorem `sound` is independent of the
number of particles, the dimension, and the analytic form of the target.
-/

namespace ThomsonCertificate

universe u v

inductive Tree (Box : Type u) where
  | leaf : Box → Tree Box
  | split : Box → Tree Box → Tree Box → Tree Box

namespace Tree

def root {Box : Type u} : Tree Box → Box
  | .leaf b => b
  | .split b _ _ => b

end Tree

structure Spec (Box : Type u) (Point : Type v) where
  inside : Box → Point → Prop
  domain : Point → Prop
  goal : Point → Prop
  terminal : Box → Prop
  splits : Box → Box → Box → Prop
  leaf_sound : ∀ b, terminal b → ∀ x, domain x → inside b x → goal x
  split_sound : ∀ b l r, splits b l r → ∀ x, inside b x → inside l x ∨ inside r x

def Checked {Box : Type u} {Point : Type v} (S : Spec Box Point) : Tree Box → Prop
  | .leaf b => S.terminal b
  | .split b l r =>
      S.splits b (Tree.root l) (Tree.root r) ∧ Checked S l ∧ Checked S r

theorem sound {Box : Type u} {Point : Type v} (S : Spec Box Point)
    (tree : Tree Box) (hchecked : Checked S tree) :
    ∀ x, S.domain x → S.inside (Tree.root tree) x → S.goal x := by
  induction tree with
  | leaf b =>
      intro x hdomain hinside
      exact S.leaf_sound b hchecked x hdomain hinside
  | split b l r ihl ihr =>
      intro x hdomain hinside
      rcases S.split_sound b (Tree.root l) (Tree.root r) hchecked.1 x hinside with hl | hr
      · exact ihl hchecked.2.1 x hdomain hl
      · exact ihr hchecked.2.2 x hdomain hr

end ThomsonCertificate
