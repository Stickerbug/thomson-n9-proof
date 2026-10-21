import ThomsonNine.PairDeriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

open scoped BigOperators InnerProductSpace
namespace ThomsonNine

/-- Derivative of a single pair term `‖(a + t v) - b‖⁻¹` in the direction `v`. -/
theorem hasDerivAt_pair_inv_dist (a b v : R3) (hab : a ≠ b) :
    HasDerivAt (fun t : ℝ => ‖(a + t • v) - b‖⁻¹) (⟪b - a, v⟫_ℝ / ‖a - b‖ ^ 3) 0 := by
  have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
  have h := hasDerivAt_inv_norm_affine (a - b) v hne
  convert h using 1
  · funext t
    rw [show (a + t • v) - b = (a - b) + t • v by abel]
  · rw [inner_sub_left, inner_sub_left]
    ring

/-- The gradient of the Coulomb energy with respect to the position of point `i`. -/
noncomputable def gradAt (x : Fin 9 → R3) (i : Fin 9) : R3 :=
  ∑ j : Fin 9, if j = i then 0 else (‖x i - x j‖ ^ 3)⁻¹ • (x j - x i)

/-- `gradAt` is the vector whose inner product with `v` is the sum of the pair terms. -/
theorem inner_gradAt (x : Fin 9 → R3) (i : Fin 9) (v : R3) :
    ⟪v, gradAt x i⟫_ℝ =
      ∑ j : Fin 9, if j = i then 0 else ⟪v, (‖x i - x j‖ ^ 3)⁻¹ • (x j - x i)⟫_ℝ := by
  unfold gradAt
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : j = i
  · simp [h]
  · simp only [h, ↓reduceIte, real_inner_smul_right]

/-- Translating all nine points leaves the Coulomb energy unchanged. -/
theorem energy_translate (x : Fin 9 → R3) (c : R3) :
    energy (fun j => x j + c) = energy x := by
  unfold energy
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [show (x a + c) - (x b + c) = x a - x b by abel]


/-- Directional derivative of the energy when only point `i` moves along `x i + t v`. -/
theorem hasDerivAt_energy_update (x : Fin 9 → R3) (hx : Function.Injective x)
    (i : Fin 9) (v : R3) :
    HasDerivAt (fun t : ℝ => energy (Function.update x i (x i + t • v)))
      (∑ a : Fin 9, ∑ b ∈ Finset.Ioi a,
        if a = i then ⟪x b - x i, v⟫_ℝ / ‖x i - x b‖ ^ 3
        else if b = i then ⟪x a - x i, v⟫_ℝ / ‖x i - x a‖ ^ 3
        else 0) 0 := by
  unfold energy
  apply HasDerivAt.fun_sum
  intro a _
  apply HasDerivAt.fun_sum
  intro b hb
  by_cases hai : a = i
  · subst hai
    have hb' : a < b := Finset.mem_Ioi.mp hb
    have hab : a ≠ b := ne_of_lt hb'
    have h := hasDerivAt_pair_inv_dist (x a) (x b) v (fun h => hab (hx h))
    simpa only [if_true, Function.update_self,
      Function.update_of_ne (ne_of_lt hb').symm] using h
  · by_cases hbi : b = i
    · rw [hbi]
      have hne : x a ≠ x i := fun h => hai (hx h)
      have h := hasDerivAt_pair_inv_dist (x a) (x i) (-v) hne
      convert h using 1
      · funext t
        simp only [Function.update_of_ne hai, Function.update_self]
        congr 1
        rw [smul_neg]
        abel
      · have hnorm : ‖x a - x i‖ = ‖x i - x a‖ := norm_sub_rev _ _
        simp only [if_neg hai, if_true, inner_neg_right, inner_sub_left, hnorm]
        ring
    · have hconst : HasDerivAt (fun _ : ℝ => ‖x a - x b‖⁻¹) 0 0 :=
        hasDerivAt_const (0 : ℝ) (‖x a - x b‖⁻¹)
      simpa only [if_neg hai, if_neg hbi, Function.update_of_ne hai,
        Function.update_of_ne hbi] using hconst


/-- Combinatorial splitting of the ordered-pair sum: the pair sum with indicators at `i`
equals the sum over all `j ≠ i`. -/
lemma sum_Ioi_ite_eq (f : Fin 9 → ℝ) (i : Fin 9) :
    (∑ a : Fin 9, ∑ b ∈ Finset.Ioi a,
      (if a = i then f b else if b = i then f a else 0))
      = ∑ j : Fin 9, if j = i then 0 else f j := by
  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
    (p := fun a : Fin 9 => a = i)]
  have h1 : (Finset.univ.filter (fun a : Fin 9 => a = i)).sum
      (fun a => ∑ b ∈ Finset.Ioi a,
        (if a = i then f b else if b = i then f a else 0))
      = ∑ b ∈ Finset.Ioi i, f b := by
    rw [Finset.sum_filter, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
  have h2 : (Finset.univ.filter (fun a : Fin 9 => ¬ a = i)).sum
      (fun a => ∑ b ∈ Finset.Ioi a,
        (if a = i then f b else if b = i then f a else 0))
      = ∑ a ∈ Finset.Iio i, f a := by
    rw [Finset.sum_filter]
    have hpt : ∀ a : Fin 9,
        (if ¬ a = i then (∑ b ∈ Finset.Ioi a,
          (if a = i then f b else if b = i then f a else 0)) else 0)
        = (if a < i then f a else 0) := by
      intro a
      by_cases hai : a = i
      · subst hai
        simp
      · rw [if_pos hai]
        have hinner : (∑ b ∈ Finset.Ioi a,
            (if a = i then f b else if b = i then f a else 0))
            = ∑ b ∈ Finset.Ioi a, (if b = i then f a else 0) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [if_neg hai]
        rw [hinner, Finset.sum_ite_eq']
        simp [Finset.mem_Ioi]
    rw [Finset.sum_congr rfl (fun a _ => hpt a)]
    rw [← Finset.sum_filter]
    congr 1
    ext a
    simp [Finset.mem_Iio]
  rw [h1, h2]
  have hR : (∑ j : Fin 9, if j = i then 0 else f j)
      = (Finset.univ.erase i).sum f := by
    rw [show (∑ j : Fin 9, if j = i then 0 else f j)
        = ∑ j : Fin 9, if j ≠ i then f j else 0 by
      refine Finset.sum_congr rfl ?_
      intro j _
      by_cases h : j = i <;> simp [h]]
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp [Finset.mem_erase]
  rw [hR]
  have herase : (Finset.univ.erase i : Finset (Fin 9)) = Finset.Iio i ∪ Finset.Ioi i := by
    ext a
    simp only [Finset.mem_erase, Finset.mem_univ, Finset.mem_union, Finset.mem_Iio,
      Finset.mem_Ioi]
    constructor
    · rintro ⟨hne, -⟩
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact ⟨ne_of_lt h, trivial⟩
      · exact ⟨ne_of_gt h, trivial⟩
  rw [herase]
  have hdisj : Disjoint (Finset.Iio i : Finset (Fin 9)) (Finset.Ioi i) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact lt_asymm (Finset.mem_Iio.mp ha) (Finset.mem_Ioi.mp hb)
  rw [Finset.sum_union hdisj, add_comm]

/-- The pair-term sum is the inner product with the gradient. -/
lemma pairSum_eq_inner_gradAt (x : Fin 9 → R3) (i : Fin 9) (v : R3) :
    (∑ j : Fin 9, if j = i then 0 else
      ⟪x j - x i, v⟫_ℝ / ‖x i - x j‖ ^ 3) = ⟪v, gradAt x i⟫_ℝ := by
  rw [inner_gradAt]
  refine Finset.sum_congr rfl ?_
  intro j _
  by_cases hj : j = i
  · simp [hj]
  · simp only [hj, ↓reduceIte, real_inner_smul_right]
    rw [div_eq_inv_mul, real_inner_comm (x j - x i) v]

/-- Directional derivative of the energy under moving one point, in gradient form. -/
theorem hasDerivAt_energy_update_gradAt (x : Fin 9 → R3) (hx : Function.Injective x)
    (i : Fin 9) (v : R3) :
    HasDerivAt (fun t : ℝ => energy (Function.update x i (x i + t • v)))
      ⟪v, gradAt x i⟫_ℝ 0 := by
  have h := hasDerivAt_energy_update x hx i v
  have hsum : (∑ a : Fin 9, ∑ b ∈ Finset.Ioi a,
        (if a = i then ⟪x b - x i, v⟫_ℝ / ‖x i - x b‖ ^ 3
        else if b = i then ⟪x a - x i, v⟫_ℝ / ‖x i - x a‖ ^ 3
        else 0)) = ⟪v, gradAt x i⟫_ℝ := by
    rw [sum_Ioi_ite_eq (fun j => ⟪x j - x i, v⟫_ℝ / ‖x i - x j‖ ^ 3) i]
    exact pairSum_eq_inner_gradAt x i v
  rwa [hsum] at h

end ThomsonNine

