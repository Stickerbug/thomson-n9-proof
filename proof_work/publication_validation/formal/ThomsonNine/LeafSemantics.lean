import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open scoped BigOperators
namespace ThomsonNine.Semantics

noncomputable def bernstein (n i : ℕ) (z : ℝ) : ℝ :=
  (n.choose i : ℝ) * z^i * (1-z)^(n-i)

theorem bernstein_nonneg (n i : ℕ) {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ bernstein n i z := by
  unfold bernstein
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz _))
    (pow_nonneg (sub_nonneg.mpr hz1) _)

noncomputable def tensor (n : ℕ) (b : Fin (n+1) → Fin (n+1) → Fin (n+1) → ℝ)
    (u v t : ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, b i j k * bernstein n i.val u *
    bernstein n j.val v * bernstein n k.val t

theorem tensor_nonneg (n : ℕ) (b : Fin (n+1) → Fin (n+1) → Fin (n+1) → ℝ)
    (hb : ∀ i j k, 0 ≤ b i j k) {u v t : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hv : 0 ≤ v) (hv1 : v ≤ 1)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) : 0 ≤ tensor n b u v t := by
  unfold tensor
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (mul_nonneg (mul_nonneg (hb i j k)
    (bernstein_nonneg n i.val hu hu1)) (bernstein_nonneg n j.val hv hv1))
    (bernstein_nonneg n k.val ht ht1)

noncomputable def gram (u v t : ℝ) : ℝ := 1 + 2*u*v*t-u^2-v^2-t^2

def physicalOrdered (u v t : ℝ) : Prop :=
  -1 ≤ u ∧ u ≤ v ∧ v ≤ t ∧ t ≤ 14/25 ∧ 0 ≤ gram u v t

theorem gram_prune {u v t : ℝ} (hg : gram u v t < 0) :
    ¬ physicalOrdered u v t := by
  intro hx
  exact (not_le_of_gt hg) hx.2.2.2.2

theorem order_prune_uv {u v t : ℝ} (h : v < u) : ¬ physicalOrdered u v t := by
  intro hx
  exact (not_le_of_gt h) hx.2.1

theorem boundary_multiplier {R g lam : ℝ} (hlam : 0 ≤ lam) (hg : 0 ≤ g)
    (h : 0 ≤ R - lam * g) : 0 ≤ R :=
  le_trans h (sub_le_self _ (mul_nonneg hlam hg))

/-- Algebraic bridge only: the two finite-sum identities remain hypotheses. -/
theorem energy_balance {E U T A D S c F111 : ℝ}
    (hT : T = 7*E-7*A-7*D-84*c)
    (hS : S = 6*A+6*D+9*F111)
    (hc : c = U/12+F111/8) : E-U = T/7+S/6 := by
  rw [hT, hS, hc]
  ring

theorem energy_lower_of_balance {E U T S : ℝ}
    (h : E-U = T/7+S/6) (hT : 0 ≤ T) (hS : 0 ≤ S) : U ≤ E := by
  apply sub_nonneg.mp
  rw [h]
  exact add_nonneg (div_nonneg hT (by norm_num)) (div_nonneg hS (by norm_num))

theorem normalized_mem_unit {l r x : ℝ} (hlr : l < r) (hlx : l ≤ x) (hxr : x ≤ r) :
    0 ≤ (x-l)/(r-l) ∧ (x-l)/(r-l) ≤ 1 := by
  constructor
  · exact div_nonneg (sub_nonneg.mpr hlx) (le_of_lt (sub_pos.mpr hlr))
  · apply (div_le_iff₀ (sub_pos.mpr hlr)).mpr
    simpa only [one_mul] using sub_le_sub_right hxr l

theorem order_prune_vt {u v t : ℝ} (h : t < v) : ¬ physicalOrdered u v t := by
  intro hx
  exact (not_le_of_gt h) hx.2.2.1

theorem order_prune_ut {u v t : ℝ} (h : t < u) : ¬ physicalOrdered u v t := by
  intro hx
  exact (not_le_of_gt h) (le_trans hx.2.1 hx.2.2.1)

theorem physical_mem_root {u v t : ℝ} (h : physicalOrdered u v t) :
    (-1 ≤ u ∧ u ≤ 14/25) ∧ (-1 ≤ v ∧ v ≤ 14/25) ∧ (-1 ≤ t ∧ t ≤ 14/25) := by
  exact ⟨⟨h.1, le_trans h.2.1 (le_trans h.2.2.1 h.2.2.2.1)⟩,
    ⟨le_trans h.1 h.2.1, le_trans h.2.2.1 h.2.2.2.1⟩,
    ⟨le_trans (le_trans h.1 h.2.1) h.2.2.1, h.2.2.2.1⟩⟩

end ThomsonNine.Semantics
