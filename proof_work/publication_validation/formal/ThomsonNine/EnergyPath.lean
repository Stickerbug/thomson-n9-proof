import ThomsonNine.EnergyGradient
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open scoped BigOperators InnerProductSpace
namespace ThomsonNine

/-- Derivative of one pair term when both endpoints move along straight paths. -/
lemma hasDerivAt_pair_inv_dist_path (a b va vb : R3) (hab : a ≠ b) :
    HasDerivAt (fun t : ℝ => ‖(a + t • va) - (b + t • vb)‖⁻¹)
      (-(⟪a - b, va - vb⟫_ℝ) / ‖a - b‖ ^ 3) 0 := by
  have h := hasDerivAt_inv_norm_affine (a - b) (va - vb) (sub_ne_zero.mpr hab)
  convert h using 1
  funext t
  rw [show (a + t • va) - (b + t • vb) = (a - b) + t • (va - vb) by
    rw [smul_sub]
    abel]

/-- Reindexing a sum over the lower triangle as a sum over the upper triangle. -/
lemma sum_Iio_swap (A : Fin 9 → Fin 9 → ℝ) :
    (∑ i : Fin 9, ∑ j ∈ Finset.Iio i, A i j)
      = ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, A j i := by
  simp only [← Finset.filter_gt_eq_Iio, ← Finset.filter_lt_eq_Ioi]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]

/-- A sum with the diagonal removed, written as a sum over `univ.erase i`. -/
lemma sum_univ_ite_eq_sum_erase (f : Fin 9 → ℝ) (i : Fin 9) :
    (∑ j : Fin 9, if j = i then 0 else f j) = (Finset.univ.erase i).sum f := by
  rw [show (∑ j : Fin 9, if j = i then 0 else f j)
      = ∑ j : Fin 9, if j ≠ i then f j else 0 by
    refine Finset.sum_congr rfl ?_
    intro j _
    by_cases h : j = i <;> simp [h]]
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp [Finset.mem_erase]

/-- Splitting the complement of a point into the elements below and above it. -/
lemma sum_erase_eq_sum_Iio_add_Ioi (f : Fin 9 → ℝ) (i : Fin 9) :
    (Finset.univ.erase i).sum f = ∑ j ∈ Finset.Iio i, f j + ∑ j ∈ Finset.Ioi i, f j := by
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
  have hdisj : Disjoint (Finset.Iio i : Finset (Fin 9)) (Finset.Ioi i) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact lt_asymm (Finset.mem_Iio.mp ha) (Finset.mem_Ioi.mp hb)
  rw [herase, Finset.sum_union hdisj]

/-- Derivative of the energy when all nine points move along straight paths. -/
theorem hasDerivAt_energy_path (x : Fin 9 → R3) (hx : Function.Injective x)
    (v : Fin 9 → R3) :
    HasDerivAt (fun t : ℝ => energy (fun i => x i + t • v i))
      (∑ i : Fin 9, ⟪v i, gradAt x i⟫_ℝ) 0 := by
  have hfun : (fun t : ℝ => energy (fun i => x i + t • v i))
      = fun t : ℝ => ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i,
          ‖(x i + t • v i) - (x j + t • v j)‖⁻¹ := by
    funext t
    unfold energy
    rfl
  rw [hfun]
  have hderiv : HasDerivAt (fun t : ℝ => ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i,
        ‖(x i + t • v i) - (x j + t • v j)‖⁻¹)
      (∑ i : Fin 9, ∑ j ∈ Finset.Ioi i,
        (-(⟪x i - x j, v i - v j⟫_ℝ) / ‖x i - x j‖ ^ 3)) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    apply HasDerivAt.fun_sum
    intro j hj
    exact hasDerivAt_pair_inv_dist_path (x i) (x j) (v i) (v j)
      (fun h => ne_of_lt (Finset.mem_Ioi.mp hj) (hx h))
  have hmain : (∑ i : Fin 9, ∑ j ∈ Finset.Ioi i,
        (-(⟪x i - x j, v i - v j⟫_ℝ) / ‖x i - x j‖ ^ 3))
      = ∑ i : Fin 9, ⟪v i, gradAt x i⟫_ℝ := by
    let A : Fin 9 → Fin 9 → ℝ :=
      fun a b => ⟪x b - x a, v a⟫_ℝ / ‖x a - x b‖ ^ 3
    calc
      (∑ i : Fin 9, ∑ j ∈ Finset.Ioi i,
          (-(⟪x i - x j, v i - v j⟫_ℝ) / ‖x i - x j‖ ^ 3))
          = ∑ i : Fin 9, (∑ j ∈ Finset.Ioi i,
                ⟪x j - x i, v i⟫_ℝ / ‖x i - x j‖ ^ 3
              + ∑ j ∈ Finset.Ioi i,
                ⟪x i - x j, v j⟫_ℝ / ‖x i - x j‖ ^ 3) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl ?_
            intro j _
            simp only [inner_sub_right, inner_sub_left]
            ring
      _ = (∑ i : Fin 9, ∑ j ∈ Finset.Ioi i,
              ⟪x j - x i, v i⟫_ℝ / ‖x i - x j‖ ^ 3)
            + (∑ i : Fin 9, ∑ j ∈ Finset.Ioi i,
              ⟪x i - x j, v j⟫_ℝ / ‖x i - x j‖ ^ 3) := by
            rw [Finset.sum_add_distrib]
      _ = (∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, A i j)
            + (∑ i : Fin 9, ∑ j ∈ Finset.Iio i, A i j) := by
            congr 1
            have hB : (∑ i : Fin 9, ∑ j ∈ Finset.Ioi i,
                  ⟪x i - x j, v j⟫_ℝ / ‖x i - x j‖ ^ 3)
                = ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, A j i := by
              refine Finset.sum_congr rfl ?_
              intro i _
              refine Finset.sum_congr rfl ?_
              intro j _
              dsimp only [A]
              rw [norm_sub_rev (x j) (x i)]
            rw [hB, ← sum_Iio_swap A]
      _ = ∑ i : Fin 9, ⟪v i, gradAt x i⟫_ℝ := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [add_comm]
            rw [← sum_erase_eq_sum_Iio_add_Ioi (A i) i]
            rw [← sum_univ_ite_eq_sum_erase (A i) i]
            exact pairSum_eq_inner_gradAt x i (v i)
  simpa only [hmain] using hderiv

end ThomsonNine
