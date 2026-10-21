import ThomsonNine.DomainCoverage
import ThomsonNine.LeafSemantics

/-! # Leaf certificates and box-tree coverage

This module assembles the *checker interface* used by the 68,063-leaf coverage
certificate of the n = 9 problem, independently of the numeric data.

A box is an axis-aligned rational rectangle `[lu,ru] × [lv,rv] × [lt,rt]` in the
ordered-variable domain.  Leaves of the tree are certified in one of two ways:

* `cert`: the residual `R` is represented on the box by a tensor Bernstein
  polynomial with all coefficients nonnegative (this is `leaf_sound` on the
  domain);
* `excl`: every point of the box violates the physical domain `D` (negative Gram,
  wrong ordering, ...), so the leaf is vacuously sound on `D`.

Splits are bisections along one of the three axes.  Then any finite binary tree
of bisections whose leaves carry such certificates proves `0 ≤ R` on the whole
physical domain, with `R` and the certificate data as inputs.

This is *logic only*: the numeric tree and the rational coefficient lists are
checked outside Lean by the exact arithmetic checker.  Nothing here asserts that
such a tree exists. -/

open ThomsonNine.Semantics
open scoped BigOperators

namespace ThomsonNine.TreeSemantics

/-- An axis-aligned box in the `(u,v,t)` cube, with real bounds. -/
structure Box3 where
  (lu lv lt ru rv rt : ℝ)
  hlu : lu < ru
  hlv : lv < rv
  hlt : lt < rt

/-- Membership of a point in a box. -/
def inBox (b : Box3) (u v t : ℝ) : Prop :=
  u ∈ Set.Icc b.lu b.ru ∧ v ∈ Set.Icc b.lv b.rv ∧ t ∈ Set.Icc b.lt b.rt

/-- Bisect a box along the `u` axis. -/
noncomputable def splitU (b : Box3) : Box3 × Box3 :=
  (⟨b.lu, b.lv, b.lt, (b.lu + b.ru) / 2, b.rv, b.rt, by linarith [b.hlu], b.hlv, b.hlt⟩,
   ⟨(b.lu + b.ru) / 2, b.lv, b.lt, b.ru, b.rv, b.rt, by linarith [b.hlu], b.hlv, b.hlt⟩)

/-- Bisect a box along the `v` axis. -/
noncomputable def splitV (b : Box3) : Box3 × Box3 :=
  (⟨b.lu, b.lv, b.lt, b.ru, (b.lv + b.rv) / 2, b.rt, b.hlu, by linarith [b.hlv], b.hlt⟩,
   ⟨b.lu, (b.lv + b.rv) / 2, b.lt, b.ru, b.rv, b.rt, b.hlu, by linarith [b.hlv], b.hlt⟩)

/-- Bisect a box along the `t` axis. -/
noncomputable def splitT (b : Box3) : Box3 × Box3 :=
  (⟨b.lu, b.lv, b.lt, b.ru, b.rv, (b.lt + b.rt) / 2, b.hlu, b.hlv, by linarith [b.hlt]⟩,
   ⟨b.lu, b.lv, (b.lt + b.rt) / 2, b.ru, b.rv, b.rt, b.hlu, b.hlv, by linarith [b.hlt]⟩)

theorem inBox_splitU (b : Box3) {u v t : ℝ} (h : inBox b u v t) :
    inBox (splitU b).1 u v t ∨ inBox (splitU b).2 u v t := by
  obtain ⟨⟨hlu, hru⟩, hv, ht⟩ := h
  have hm1 : b.lu ≤ (b.lu + b.ru) / 2 := by linarith
  have hm2 : (b.lu + b.ru) / 2 ≤ b.ru := by linarith
  rcases le_total u ((b.lu + b.ru) / 2) with h' | h'
  · exact Or.inl ⟨⟨hlu, h'⟩, hv, ht⟩
  · exact Or.inr ⟨⟨h', hru⟩, hv, ht⟩

theorem inBox_splitV (b : Box3) {u v t : ℝ} (h : inBox b u v t) :
    inBox (splitV b).1 u v t ∨ inBox (splitV b).2 u v t := by
  obtain ⟨hu, ⟨hlv, hrv⟩, ht⟩ := h
  have hm1 : b.lv ≤ (b.lv + b.rv) / 2 := by linarith
  have hm2 : (b.lv + b.rv) / 2 ≤ b.rv := by linarith
  rcases le_total v ((b.lv + b.rv) / 2) with h' | h'
  · exact Or.inl ⟨hu, ⟨hlv, h'⟩, ht⟩
  · exact Or.inr ⟨hu, ⟨h', hrv⟩, ht⟩

theorem inBox_splitT (b : Box3) {u v t : ℝ} (h : inBox b u v t) :
    inBox (splitT b).1 u v t ∨ inBox (splitT b).2 u v t := by
  obtain ⟨hu, hv, ⟨hlt, hrt⟩⟩ := h
  have hm1 : b.lt ≤ (b.lt + b.rt) / 2 := by linarith
  have hm2 : (b.lt + b.rt) / 2 ≤ b.rt := by linarith
  rcases le_total t ((b.lt + b.rt) / 2) with h' | h'
  · exact Or.inl ⟨hu, hv, ⟨hlt, h'⟩⟩
  · exact Or.inr ⟨hu, hv, ⟨h', hrt⟩⟩

/-- The concurrent bisection relation: the children are the halves of the parent
along one coordinate axis. -/
def Bisect (b l r : Box3) : Prop :=
  (l = (splitU b).1 ∧ r = (splitU b).2) ∨
  (l = (splitV b).1 ∧ r = (splitV b).2) ∨
  (l = (splitT b).1 ∧ r = (splitT b).2)

theorem bisect_sound {b l r : Box3} (h : Bisect b l r) {u v t : ℝ}
    (hin : inBox b u v t) : inBox l u v t ∨ inBox r u v t := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact inBox_splitU b hin
  · exact inBox_splitV b hin
  · exact inBox_splitT b hin

/-- Terminal certificates accepted at the leaves. -/
inductive Terminal (R : ℝ → ℝ → ℝ → ℝ) : Box3 → Prop where
  /-- A tensor-Bernstein certificate with nonnegative coefficients. -/
  | cert (b : Box3) (n : ℕ) (coeff : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℝ)
      (hnonneg : ∀ i j k, 0 ≤ coeff i j k)
      (hrepr : ∀ u v t, inBox b u v t →
        R u v t = tensor n coeff ((u - b.lu) / (b.ru - b.lu))
          ((v - b.lv) / (b.rv - b.lv)) ((t - b.lt) / (b.rt - b.lt)))
      : Terminal R b
  /-- An exclusion leaf: the whole box is outside the physical domain. -/
  | excl (b : Box3) (h : ∀ u v t, inBox b u v t → ¬ physicalOrdered u v t)
      : Terminal R b

/-- Every terminal certificate is sound on the physical domain. -/
theorem terminal_sound {R : ℝ → ℝ → ℝ → ℝ} {b : Box3} (T : Terminal R b) :
    ∀ u v t, physicalOrdered u v t → inBox b u v t → 0 ≤ R u v t := by
  intro u v t hD hin
  cases T with
  | cert n coeff hnn hrepr =>
    rw [hrepr u v t hin]
    obtain ⟨hu0, hu1⟩ := normalized_mem_unit b.hlu hin.1.1 hin.1.2
    obtain ⟨hv0, hv1⟩ := normalized_mem_unit b.hlv hin.2.1.1 hin.2.1.2
    obtain ⟨ht0, ht1⟩ := normalized_mem_unit b.hlt hin.2.2.1 hin.2.2.2
    exact tensor_nonneg n coeff hnn hu0 hu1 hv0 hv1 ht0 ht1
  | excl h => exact absurd hD (h u v t hin)

/-- **Coverage soundness for the sharp tree.**  If a finite binary tree of
bisections has every leaf certified by `Terminal R`, then throughout the physical
domain inside the root box the residual is nonnegative. -/
theorem covered_sound {R : ℝ → ℝ → ℝ → ℝ} {tree : Coverage.Tree Box3}
    (checked : Coverage.Checked (Terminal R) Bisect tree) :
    ∀ u v t, physicalOrdered u v t → inBox (Coverage.root tree) u v t → 0 ≤ R u v t := by
  have h := Coverage.coverage_sound_on_domain (Box := Box3) (Point := ℝ × ℝ × ℝ)
    (fun b (p : ℝ × ℝ × ℝ) => inBox b p.1 p.2.1 p.2.2)
    (fun p : ℝ × ℝ × ℝ => physicalOrdered p.1 p.2.1 p.2.2)
    (fun p : ℝ × ℝ × ℝ => 0 ≤ R p.1 p.2.1 p.2.2)
    (Terminal R) Bisect
    (by intro b T p hD hin; exact terminal_sound T p.1 p.2.1 p.2.2 hD hin)
    (by intro b l r hs p hin; exact bisect_sound hs hin)
    tree checked
  intro u v t hD hin
  exact h (u, v, t) hD hin

/-- The root box of the sharp certificate: `[-1, 14/25]³`. -/
noncomputable def rootBox : Box3 :=
  ⟨-1, -1, -1, 14/25, 14/25, 14/25, by norm_num, by norm_num, by norm_num⟩

/-- Every point of the physical domain lies in the root box. -/
theorem physicalOrdered_mem_rootBox {u v t : ℝ} (h : physicalOrdered u v t) :
    inBox rootBox u v t := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨⟨h1, le_trans h2 (le_trans h3 h4)⟩,
    ⟨le_trans h1 h2, le_trans h3 h4⟩,
    ⟨le_trans h1 (le_trans h2 h3), h4⟩⟩

/-- **Coverage from the sharp root box.**  If the checked tree is rooted at the
certificate's root box `[-1, 14/25]³` and its leaves carry terminal certificates,
then the residual is nonnegative on the whole physical domain. -/
theorem covered_sound_root {R : ℝ → ℝ → ℝ → ℝ} {tree : Coverage.Tree Box3}
    (hroot : Coverage.root tree = rootBox)
    (checked : Coverage.Checked (Terminal R) Bisect tree) :
    ∀ u v t, physicalOrdered u v t → 0 ≤ R u v t := by
  intro u v t hD
  have hin : inBox (Coverage.root tree) u v t := by
    rw [hroot]; exact physicalOrdered_mem_rootBox hD
  exact covered_sound checked u v t hD hin

end ThomsonNine.TreeSemantics
