/-
The combinatorial and matrix-kernel infrastructure of the Bachoc--Valentín
three-point bound, adapted with attribution from the N=7 Lean development
`huwngtran/thomson-n7-lean` (commit 25f2fa53119273458cfbb3c4230904bffdd61e53),
file `Solution.lean`, sections `Comb`, `Comb2`, `Comb3`, `Comb4`, `Final`.

This port contains the reduced-kernel combinatorics (`dsum`, `Rs`, `dsum_Rs`,
`dsum_H`), the Gram-OK region, and the matrix kernel `Rk` with its dot-product
reductions, and the exact three-point identity `three_point_identity`.
It does NOT contain `three_point_bound`: that needs the PSD moment
inequality `matDot_moment_nonneg`, whose Mathlib ingredient
`Matrix.posSemidef_iff_eq_sum_vecMulVec` is not available in the pinned cache.

The `omega` calls of the original were replaced by elementary Nat lemmas.
-/
import ThomsonNine.ThreePoint
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace ThomsonNine.ThreePoint

section Comb

variable {n : ℕ}

/-- Sum over ordered triples of pairwise distinct indices. -/
def dsum (f : Fin n → Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ l, if i ≠ j ∧ i ≠ l ∧ j ≠ l then f i j l else 0

theorem sum_all_eq (f : Fin n → Fin n → Fin n → ℝ) :
    ∑ i, ∑ j, ∑ l, f i j l
      = dsum f + ∑ i, ∑ l, f i i l + ∑ i, ∑ j, f i j i + ∑ i, ∑ j, f i j j
          - 2 * ∑ i, f i i i := by
  have pt : ∀ i j l, f i j l
      = (if i ≠ j ∧ i ≠ l ∧ j ≠ l then f i j l else 0) + (if i = j then f i j l else 0)
        + (if i = l then f i j l else 0) + (if j = l then f i j l else 0)
        - 2 * (if i = j then (if j = l then f i j l else 0) else 0) := by
    intro i j l
    by_cases h1 : i = j <;> by_cases h2 : i = l <;> by_cases h3 : j = l <;> simp_all <;> ring
  have e1 : ∑ i, ∑ j, ∑ l, (if i = j then f i j l else 0) = ∑ i, ∑ l, f i i l := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    simp [Finset.sum_ite_eq]
  have e2 : ∑ i, ∑ j, ∑ l, (if i = l then f i j l else 0) = ∑ i, ∑ j, f i j i := by
    simp [Finset.sum_ite_eq]
  have e3 : ∑ i, ∑ j, ∑ l, (if j = l then f i j l else 0) = ∑ i, ∑ j, f i j j := by
    simp [Finset.sum_ite_eq]
  have e4 : ∑ i, ∑ j, ∑ l, (if i = j then (if j = l then f i j l else 0) else 0)
      = ∑ i, f i i i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    simp [Finset.sum_ite_eq]
  calc ∑ i, ∑ j, ∑ l, f i j l
      = ∑ i, ∑ j, ∑ l, ((if i ≠ j ∧ i ≠ l ∧ j ≠ l then f i j l else 0) + (if i = j then f i j l else 0)
        + (if i = l then f i j l else 0) + (if j = l then f i j l else 0)
        - 2 * (if i = j then (if j = l then f i j l else 0) else 0)) := by
          simp only [← pt]
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, e1, e2, e3, e4]
      rfl

end Comb

section Comb2

variable {n : ℕ}

theorem dsum_mono {f g : Fin n → Fin n → Fin n → ℝ}
    (h : ∀ i j l, i ≠ j → i ≠ l → j ≠ l → f i j l ≤ g i j l) : dsum f ≤ dsum g := by
  unfold dsum
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => ?_
  split_ifs with hc
  · exact h i j l hc.1 hc.2.1 hc.2.2
  · exact le_rfl

theorem dsum_add (f g : Fin n → Fin n → Fin n → ℝ) :
    dsum (fun i j l => f i j l + g i j l) = dsum f + dsum g := by
  unfold dsum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp

theorem dsum_sub (f g : Fin n → Fin n → Fin n → ℝ) :
    dsum (fun i j l => f i j l - g i j l) = dsum f - dsum g := by
  unfold dsum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp

theorem dsum_mul_left (c : ℝ) (f : Fin n → Fin n → Fin n → ℝ) :
    dsum (fun i j l => c * f i j l) = c * dsum f := by
  unfold dsum
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp

theorem dsum_swap23 (f : Fin n → Fin n → Fin n → ℝ) :
    dsum (fun i j l => f i l j) = dsum f := by
  unfold dsum
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : i ≠ a ∧ i ≠ b ∧ a ≠ b
  · rw [ite_eq_left h, ite_eq_left ⟨h.2.1, h.1, h.2.2.symm⟩]
  · rw [ite_eq_right h, ite_eq_right]
    rintro ⟨h1, h2, h3⟩
    exact h ⟨h2, h1, h3.symm⟩

theorem dsum_cyc (f : Fin n → Fin n → Fin n → ℝ) :
    dsum (fun i j l => f j l i) = dsum f := by
  unfold dsum
  calc ∑ i, ∑ j, ∑ l, (if i ≠ j ∧ i ≠ l ∧ j ≠ l then f j l i else 0)
      = ∑ j, ∑ i, ∑ l, (if i ≠ j ∧ i ≠ l ∧ j ≠ l then f j l i else 0) := Finset.sum_comm
    _ = ∑ j, ∑ l, ∑ i, (if i ≠ j ∧ i ≠ l ∧ j ≠ l then f j l i else 0) :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun c _ => ?_
      by_cases h : a ≠ b ∧ a ≠ c ∧ b ≠ c
      · rw [ite_eq_left ⟨h.2.1.symm, h.2.2.symm, h.1⟩, ite_eq_left h]
      · rw [ite_eq_right, ite_eq_right h]
        rintro ⟨h1, h2, h3⟩
        exact h ⟨h3, h1.symm, h2.symm⟩

theorem card_third (hn : 2 ≤ n) (i j : Fin n) (hij : i ≠ j) :
    (Finset.univ.filter fun l : Fin n => i ≠ j ∧ i ≠ l ∧ j ≠ l).card = n - 2 := by
  have h : (Finset.univ.filter fun l : Fin n => i ≠ j ∧ i ≠ l ∧ j ≠ l)
      = (Finset.univ.erase i).erase j := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq]
    constructor
    · rintro ⟨_, h2, h3⟩
      exact ⟨fun h => h3 h.symm, fun h => h2 h.symm, trivial⟩
    · rintro ⟨h3, h2, _⟩
      exact ⟨hij, fun h => h2 h.symm, fun h => h3 h.symm⟩
  rw [h, Finset.card_erase_of_mem (by simp [hij.symm]), Finset.card_erase_of_mem (Finset.mem_univ i)]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [Nat.sub_sub]

theorem dsum_pair12 (hn : 2 ≤ n) (g : Fin n → Fin n → ℝ) :
    dsum (fun i j _ => g i j)
      = ((n : ℝ) - 2) * ∑ i, ∑ j, (if i ≠ j then g i j else 0) := by
  unfold dsum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hij : i = j
  · simp [hij]
  · rw [ite_eq_left hij, ← Finset.sum_filter, Finset.sum_const, card_third hn i j hij, nsmul_eq_mul]
    push_cast [Nat.cast_sub hn]
    ring

theorem dsum_pair13 (hn : 2 ≤ n) (g : Fin n → Fin n → ℝ) :
    dsum (fun i _ l => g i l)
      = ((n : ℝ) - 2) * ∑ i, ∑ j, (if i ≠ j then g i j else 0) :=
  (dsum_swap23 (fun i j _ => g i j)).trans (dsum_pair12 hn g)

theorem dsum_pair23 (hn : 2 ≤ n) (g : Fin n → Fin n → ℝ) :
    dsum (fun _ j l => g j l)
      = ((n : ℝ) - 2) * ∑ i, ∑ j, (if i ≠ j then g i j else 0) :=
  (dsum_cyc (fun i j _ => g i j)).trans (dsum_pair12 hn g)

theorem dsum_const (hn : 2 ≤ n) (c : ℝ) :
    dsum (n := n) (fun _ _ _ => c) = c * ((n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2)) := by
  rw [dsum_pair12 hn (fun _ _ => c)]
  have h1 : ∀ i : Fin n, ∑ j : Fin n, (if i ≠ j then c else 0) = c * ((n : ℝ) - 1) := by
    intro i
    rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_ne,
      Finset.card_erase_of_mem (Finset.mem_univ i), nsmul_eq_mul]
    simp only [Finset.card_univ, Fintype.card_fin]
    push_cast [Nat.cast_sub (show 1 ≤ n by exact le_trans (by norm_num : (1:ℕ) ≤ 2) hn)]
    ring
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end Comb2

section Comb3

variable {n : ℕ}

theorem sum_ne_eq_two_sum_Ioi (h : Fin n → Fin n → ℝ) (hsymm : ∀ i j, h i j = h j i) :
    ∑ i, ∑ j, (if i ≠ j then h i j else 0) = 2 * ∑ i, ∑ j ∈ Finset.Ioi i, h i j := by
  have step1 : ∀ i : Fin n, ∑ j, (if i ≠ j then h i j else 0)
      = ∑ j, (if i < j then h i j else 0) + ∑ j, (if j < i then h i j else 0) := by
    intro i
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rcases lt_trichotomy i j with hlt | heq | hgt
    · simp [hlt, hlt.ne, not_lt_of_gt hlt]
    · simp [heq]
    · simp [hgt, hgt.ne', not_lt_of_gt hgt]
  have hI : ∀ i : Fin n, ∑ j, (if i < j then h i j else 0) = ∑ j ∈ Finset.Ioi i, h i j := by
    intro i
    rw [← Finset.sum_filter, Finset.filter_lt_eq_Ioi]
  simp only [step1, Finset.sum_add_distrib, hI]
  have h2 : ∑ i : Fin n, ∑ j, (if j < i then h i j else 0)
      = ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, h i j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_filter, Finset.filter_lt_eq_Ioi]
    exact Finset.sum_congr rfl fun i _ => hsymm i j
  rw [h2]
  ring

end Comb3

section Comb4

variable {n : ℕ}

/-- The scalar reduced kernel: the marginal terms are chosen so that the sum over ordered
distinct triples is `(n - 2)` times the sum over all triples. -/
noncomputable def Rs (s : ℝ → ℝ → ℝ → ℝ) (n : ℕ) (u v t : ℝ) : ℝ :=
  ((n : ℝ) - 2) * s u v t + (s u u 1 + s v v 1 + s t t 1) + s 1 1 1 / ((n : ℝ) - 1)

theorem sum_ne_eq_sub (a : Fin n → ℝ) (i : Fin n) :
    ∑ j, (if i ≠ j then a j else 0) = ∑ j, a j - a i := by
  have h1 : ∑ j, a j = ∑ j, (if i ≠ j then a j else 0) + ∑ j, (if i = j then a j else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : i = j <;> simp [h]
  rw [h1, Finset.sum_ite_eq]
  simp

theorem dsum_Rs (hn : 3 ≤ n) (s : ℝ → ℝ → ℝ → ℝ)
    (hs12 : ∀ u v t, s u v t = s v u t) (hs23 : ∀ u v t, s u v t = s u t v)
    (τ : Fin n → Fin n → ℝ) (hsymm : ∀ i j, τ i j = τ j i) (hdiag : ∀ i, τ i i = 1) :
    dsum (fun i j l => Rs s n (τ i j) (τ i l) (τ j l))
      = ((n : ℝ) - 2) * ∑ i, ∑ j, ∑ l, s (τ i j) (τ i l) (τ j l) := by
  have hn2 : 2 ≤ n := le_trans (by norm_num : (2:ℕ) ≤ 3) hn
  have hn1 : ((n : ℝ) - 1) ≠ 0 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    intro h
    linarith
  obtain ⟨g, hg⟩ : ∃ g : Fin n → Fin n → ℝ, ∀ i j, g i j = s (τ i j) (τ i j) 1 :=
    ⟨fun i j => s (τ i j) (τ i j) 1, fun _ _ => rfl⟩
  have hgd : ∀ i, g i i = s 1 1 1 := by intro i; rw [hg, hdiag]
  have hQ : ∑ i, ∑ j, (if i ≠ j then g i j else 0)
      = ∑ i, ∑ j, g i j - (n : ℝ) * s 1 1 1 := by
    simp only [sum_ne_eq_sub, hgd, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hall := sum_all_eq (n := n) (fun i j l => s (τ i j) (τ i l) (τ j l))
  have e1 : ∑ i, ∑ l, s (τ i i) (τ i l) (τ i l) = ∑ i, ∑ j, g i j := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    rw [hdiag i, hs12 1 (τ i l) (τ i l), hs23 (τ i l) 1 (τ i l), hg]
  have e2 : ∑ i, ∑ j, s (τ i j) (τ i i) (τ j i) = ∑ i, ∑ j, g i j := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hdiag i, hsymm j i, hs23 (τ i j) 1 (τ i j), hg]
  have e3 : ∑ i, ∑ j, s (τ i j) (τ i j) (τ j j) = ∑ i, ∑ j, g i j := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hdiag j, hg]
  have e4 : ∑ i, s (τ i i) (τ i i) (τ i i) = (n : ℝ) * s 1 1 1 := by
    simp only [hdiag, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hR : dsum (fun i j l => Rs s n (τ i j) (τ i l) (τ j l))
      = ((n : ℝ) - 2) * dsum (fun i j l => s (τ i j) (τ i l) (τ j l))
        + (dsum (fun i j _ => g i j) + dsum (fun i _ l => g i l) + dsum (fun _ j l => g j l))
        + dsum (n := n) (fun _ _ _ => s 1 1 1 / ((n : ℝ) - 1)) := by
    have hfun : (fun i j l => Rs s n (τ i j) (τ i l) (τ j l))
        = fun i j l => (((n : ℝ) - 2) * s (τ i j) (τ i l) (τ j l) + (g i j + g i l + g j l))
            + s 1 1 1 / ((n : ℝ) - 1) := by
      funext i j l
      simp only [Rs, hg]
    rw [hfun, dsum_add, dsum_add, dsum_mul_left, dsum_add, dsum_add]
  rw [hR, dsum_pair12 hn2, dsum_pair13 hn2, dsum_pair23 hn2, dsum_const hn2, hQ, hall, e1, e2, e3,
    e4]
  field_simp
  ring

theorem dsum_H (hn : 3 ≤ n) (H : ℝ → ℝ) (c : ℝ) (τ : Fin n → Fin n → ℝ)
    (hsymm : ∀ i j, τ i j = τ j i) :
    dsum (fun i j l => (H (τ i j) + H (τ i l) + H (τ j l)) / 3 - c)
      = 2 * ((n : ℝ) - 2) * ∑ i, ∑ j ∈ Finset.Ioi i, H (τ i j)
        - c * ((n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2)) := by
  have hn2 : 2 ≤ n := le_trans (by norm_num : (2:ℕ) ≤ 3) hn
  have hfun : (fun i j l => (H (τ i j) + H (τ i l) + H (τ j l)) / 3 - c)
      = fun i j l => (1 / 3 : ℝ) * (H (τ i j) + H (τ i l) + H (τ j l)) - c := by
    funext i j l; ring
  rw [hfun, dsum_sub, dsum_mul_left, dsum_add, dsum_add,
    dsum_pair12 hn2 (fun i j => H (τ i j)), dsum_pair13 hn2 (fun i j => H (τ i j)),
    dsum_pair23 hn2 (fun i j => H (τ i j)), dsum_const hn2,
    sum_ne_eq_two_sum_Ioi (fun i j => H (τ i j)) (fun i j => by rw [hsymm])]
  ring

end Comb4

section Final

variable {n : ℕ}

theorem dsum_nonneg {f : Fin n → Fin n → Fin n → ℝ}
    (h : ∀ i j l, i ≠ j → i ≠ l → j ≠ l → 0 ≤ f i j l) : 0 ≤ dsum f := by
  unfold dsum
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ => ?_
  split_ifs with hc
  · exact h i j l hc.1 hc.2.1 hc.2.2
  · exact le_rfl

theorem inner_coords (x y : R3) : ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

theorem normsq_coords (x : R3) (hx : ‖x‖ = 1) : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = 1 := by
  have := real_inner_self_eq_norm_sq x
  rw [hx, inner_coords] at this
  nlinarith [this]

/-- The Gram determinant of three unit vectors in `ℝ³` is a square, hence nonnegative. -/
theorem gram_det_nonneg (x y z : R3) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1) :
    0 ≤ 1 + 2 * ⟪x, y⟫ * ⟪x, z⟫ * ⟪y, z⟫ - ⟪x, y⟫ ^ 2 - ⟪x, z⟫ ^ 2 - ⟪y, z⟫ ^ 2 := by
  have hx' := normsq_coords x hx; have hy' := normsq_coords y hy; have hz' := normsq_coords z hz
  rw [inner_coords, inner_coords, inner_coords]
  have key : 1 + 2 * (x 0 * y 0 + x 1 * y 1 + x 2 * y 2) * (x 0 * z 0 + x 1 * z 1 + x 2 * z 2)
        * (y 0 * z 0 + y 1 * z 1 + y 2 * z 2) - (x 0 * y 0 + x 1 * y 1 + x 2 * y 2) ^ 2
        - (x 0 * z 0 + x 1 * z 1 + x 2 * z 2) ^ 2 - (y 0 * z 0 + y 1 * z 1 + y 2 * z 2) ^ 2
      = (x 0 * (y 1 * z 2 - y 2 * z 1) - x 1 * (y 0 * z 2 - y 2 * z 0)
          + x 2 * (y 0 * z 1 - y 1 * z 0)) ^ 2 := by
    linear_combination
      (2*y 0^2*z 0^2 - y 0^2 + 2*y 0*y 1*z 0*z 1 + 2*y 0*y 2*z 0*z 2 - y 1^2*z 2^2
        + 2*y 1*y 2*z 1*z 2 - y 2^2*z 1^2 - z 0^2) * hx'
      + (2*x 0*x 1*z 0*z 1 + 2*x 0*x 2*z 0*z 2 - 2*x 1^2*z 0^2 - x 1^2*z 2^2 + x 1^2
        + 2*x 1*x 2*z 1*z 2 - 2*x 2^2*z 0^2 - x 2^2*z 1^2 + x 2^2 + z 0^2 - 1) * hy'
      + (2*x 0*x 1*y 0*y 1 + 2*x 0*x 2*y 0*y 2 + 2*x 1^2*y 1^2 + x 1^2*y 2^2 - x 1^2
        + 2*x 1*x 2*y 1*y 2 + x 2^2*y 1^2 + 2*x 2^2*y 2^2 - x 2^2 - y 1^2 - y 2^2) * hz'
  rw [key]; positivity

/-- The region of triples `(u, v, t)` of inner products of three unit vectors of `ℝ³`
(Gram matrix positive semidefinite). -/
def GramOK (u v t : ℝ) : Prop :=
  u ^ 2 ≤ 1 ∧ v ^ 2 ≤ 1 ∧ t ^ 2 ≤ 1 ∧ 0 ≤ 1 + 2 * u * v * t - u ^ 2 - v ^ 2 - t ^ 2

theorem gramOK_inner (x y z : R3) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1) :
    GramOK ⟪x, y⟫ ⟪x, z⟫ ⟪y, z⟫ := by
  have h1 : ∀ a b : R3, ‖a‖ = 1 → ‖b‖ = 1 → ⟪a, b⟫ ^ 2 ≤ 1 := by
    intro a b ha hb
    have := abs_real_inner_le_norm a b
    rw [ha, hb, mul_one] at this
    exact (sq_le_one_iff_abs_le_one _).mpr this
  refine ⟨h1 x y hx hy, h1 x z hx hz, h1 y z hy hz, ?_⟩
  have := gram_det_nonneg x y z hx hy hz
  linarith

theorem matDot_add {m : ℕ} (F A B : Matrix (Fin m) (Fin m) ℝ) :
    matDot F (A + B) = matDot F A + matDot F B := by
  simp only [matDot, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem matDot_smul {m : ℕ} (F A : Matrix (Fin m) (Fin m) ℝ) (c : ℝ) :
    matDot F (c • A) = c * matDot F A := by
  simp only [matDot, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- The reduced matrix kernel `R_k` for `n` points. -/
noncomputable def Rk (n m k : ℕ) (u v t : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  ((n : ℝ) - 2) • S3 m k u v t + (S3 m k u u 1 + S3 m k v v 1 + S3 m k t t 1)
    + (1 / ((n : ℝ) - 1)) • S3 m k 1 1 1

theorem matDot_Rk {m : ℕ} (F : Matrix (Fin m) (Fin m) ℝ) (n k : ℕ) (u v t : ℝ) :
    matDot F (Rk n m k u v t) = Rs (fun u v t => matDot F (S3 m k u v t)) n u v t := by
  simp only [Rk, Rs, matDot_add, matDot_smul]
  ring

theorem sum_matDot_Rk (K n : ℕ) (m : ℕ → ℕ)
    (F : (k : ℕ) → Matrix (Fin (m k)) (Fin (m k)) ℝ) (u v t : ℝ) :
    ∑ k ∈ Finset.range K, matDot (F k) (Rk n (m k) k u v t)
      = Rs (fun u v t => ∑ k ∈ Finset.range K, matDot (F k) (S3 (m k) k u v t)) n u v t := by
  simp only [matDot_Rk, Rs, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div]

theorem sum4_swap {ι κ : Type*} [Fintype ι] (s : Finset κ) (f : ι → ι → ι → κ → ℝ) :
    ∑ i, ∑ j, ∑ l, ∑ k ∈ s, f i j l k = ∑ k ∈ s, ∑ i, ∑ j, ∑ l, f i j l k := by
  calc ∑ i, ∑ j, ∑ l, ∑ k ∈ s, f i j l k
      = ∑ i, ∑ j, ∑ k ∈ s, ∑ l, f i j l k :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ i, ∑ k ∈ s, ∑ j, ∑ l, f i j l k := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k ∈ s, ∑ i, ∑ j, ∑ l, f i j l k := Finset.sum_comm

/-- **Three-point identity** (adapted from the N=7 formalization). -/
theorem three_point_identity (hn : 3 ≤ n) (s : ℝ → ℝ → ℝ → ℝ)
    (hs12 : ∀ u v t, s u v t = s v u t) (hs23 : ∀ u v t, s u v t = s u t v)
    (H : ℝ → ℝ) (e : ℝ) (x : Fin n → R3) (hx : ∀ i, ‖x i‖ = 1) :
    dsum (fun i j l => ((H ⟪x i, x j⟫ + H ⟪x i, x l⟫ + H ⟪x j, x l⟫) / 3
        - e / (n.choose 2 : ℝ)) - Rs s n ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫)
      + ((n : ℝ) - 2) * ∑ i, ∑ j, ∑ l, s ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫
    = 2 * ((n : ℝ) - 2) * (∑ i, ∑ j ∈ Finset.Ioi i, H ⟪x i, x j⟫ - e) := by
  have hsymm : ∀ i j, ⟪x i, x j⟫ = ⟪x j, x i⟫ := fun i j => (real_inner_comm _ _).symm
  have hdiag : ∀ i, ⟪x i, x i⟫ = 1 := fun i => by
    rw [real_inner_self_eq_norm_sq, hx i]; norm_num
  rw [dsum_sub, dsum_Rs hn s hs12 hs23 (fun i j => ⟪x i, x j⟫) hsymm hdiag,
    dsum_H hn H (e / (n.choose 2 : ℝ)) (fun i j => ⟪x i, x j⟫) hsymm]
  have hc : (n.choose 2 : ℝ) = n * (n - 1) / 2 := Nat.cast_choose_two ℝ n
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : ((n : ℝ) - 1) ≠ 0 := by intro h; linarith
  have hn0 : (n : ℝ) ≠ 0 := by intro h; linarith
  rw [hc]
  field_simp
  ring

/-- Pairing of a PSD matrix with the moment matrix is nonnegative, in the
*witnessed* form: the matrix is given as an explicit sum of rank-one squares
`∑ s, vecMulVec (v s) (v s)` instead of an abstract `PosSemidef` hypothesis.
This is the form in which a certificate can be checked: the vectors `v s` are
the explicit SOS coefficients. -/
theorem matDot_moment_nonneg_sos (m k : ℕ) {n : ℕ} (x : Fin n → R3)
    (hx : ∀ i, ‖x i‖ = 1) (r : ℕ) (v : Fin r → Fin m → ℝ) :
    0 ≤ ∑ i, ∑ j, ∑ l,
        matDot (∑ s, Matrix.vecMulVec (v s) (v s))
          (S3 m k ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫) := by
  have key3 : ∀ X : Fin m → Fin m → Fin r → ℝ,
      ∑ a, ∑ b, ∑ s, X a b s = ∑ s, ∑ a, ∑ b, X a b s := by
    intro X
    calc ∑ a, ∑ b, ∑ s, X a b s = ∑ a, ∑ s, ∑ b, X a b s :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ s, ∑ a, ∑ b, X a b s := Finset.sum_comm
  have hdot : ∀ M : Matrix (Fin m) (Fin m) ℝ,
      matDot (∑ s, Matrix.vecMulVec (v s) (v s)) M
        = ∑ s, v s ⬝ᵥ M.mulVec (v s) := by
    intro M
    simp only [matDot, Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply, star_trivial,
      dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
    rw [key3 (fun a b s => v s a * v s b * M a b)]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => ?_
    ring
  simp only [hdot]
  rw [sum4_swap (s := Finset.univ)
    (f := fun i j l s => v s ⬝ᵥ (S3 m k ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫).mulVec (v s))]
  exact Finset.sum_nonneg fun s _ => bv_positivity m k x hx (v s)

/-- **Three-point bound** in witnessed SOS form: if the matrices `F k` are given
by explicit sums of rank-one squares, then the Bachoc--Valentín bound holds.

This is `three_point_bound` of the N=7 development with the `PosSemidef`
hypothesis replaced by its witnessed decomposition, so that the certificate
data (SOS vectors) can in principle be checked by computation. -/
theorem three_point_bound_sos (hn : 3 ≤ n) (K : ℕ) (m : ℕ → ℕ)
    (F : (k : ℕ) → Matrix (Fin (m k)) (Fin (m k)) ℝ)
    (hF : ∀ k, k < K → ∃ (r : ℕ) (v : Fin r → Fin (m k) → ℝ),
      F k = ∑ s, Matrix.vecMulVec (v s) (v s))
    (H : ℝ → ℝ) (e : ℝ)
    (hpt : ∀ u v t : ℝ, GramOK u v t →
      ∑ k ∈ Finset.range K, matDot (F k) (Rk n (m k) k u v t)
        ≤ (H u + H v + H t) / 3 - e / (n.choose 2 : ℝ))
    (x : Fin n → R3) (hx : ∀ i, ‖x i‖ = 1) :
    e ≤ ∑ i, ∑ j ∈ Finset.Ioi i, H ⟪x i, x j⟫ := by
  set s : ℝ → ℝ → ℝ → ℝ := fun u v t =>
    ∑ k ∈ Finset.range K, matDot (F k) (S3 (m k) k u v t) with hs
  have hs12 : ∀ u v t, s u v t = s v u t := fun u v t => by
    simp only [hs, S3_swap12 _ _ u v t]
  have hs23 : ∀ u v t, s u v t = s u t v := fun u v t => by
    simp only [hs, S3_swap23 _ _ u v t]
  have hid := three_point_identity hn s hs12 hs23 H e x hx
  have hBV : 0 ≤ ∑ i, ∑ j, ∑ l, s ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫ := by
    simp only [hs]
    rw [sum4_swap (s := Finset.range K)
      (f := fun i j l k =>
        matDot (F k) (S3 (m k) k ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫))]
    refine Finset.sum_nonneg fun k hk => ?_
    obtain ⟨r, v, hv⟩ := hF k (Finset.mem_range.mp hk)
    rw [hv]
    exact matDot_moment_nonneg_sos (m k) k x hx r v
  have hslack : 0 ≤ dsum (fun i j l => ((H ⟪x i, x j⟫ + H ⟪x i, x l⟫ + H ⟪x j, x l⟫) / 3
        - e / (n.choose 2 : ℝ)) - Rs s n ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫) := by
    refine dsum_nonneg fun i j l _ _ _ => ?_
    have := hpt _ _ _ (gramOK_inner (x i) (x j) (x l) (hx i) (hx j) (hx l))
    rw [sum_matDot_Rk] at this
    linarith
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < 2 * ((n : ℝ) - 2) := by linarith
  have hprod : 0 ≤ 2 * ((n : ℝ) - 2) * (∑ i, ∑ j ∈ Finset.Ioi i, H ⟪x i, x j⟫ - e) := by
    rw [← hid]
    have : 0 ≤ ((n : ℝ) - 2) * ∑ i, ∑ j, ∑ l, s ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫ :=
      mul_nonneg (by linarith) hBV
    linarith
  have := nonneg_of_mul_nonneg_right hprod hpos
  linarith

end Final
