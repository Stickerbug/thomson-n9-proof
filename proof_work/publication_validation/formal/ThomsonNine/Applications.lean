import ThomsonNine.Minimum
import ThomsonNine.EnergyContinuity
import Mathlib.Analysis.Normed.Operator.LinearIsometry

open ThomsonNine
open ThomsonNine.Family
open scoped BigOperators InnerProductSpace

namespace ThomsonNine

/-! First applications of the formalized energy functional:

* invariance under a linear isometry of the ambient space;
* a crude but unconditional lower bound for the nine-point energy on the sphere;
* the energy along the candidate curve has derivative `familyEnergyDeriv`;
* the sphere configuration space is nonempty (the candidate provides a point). -/

theorem energy_comp_isometry {n : ℕ} (x : Fin n → R3) (f : R3 ≃ₗᵢ[ℝ] R3) :
    energy (f ∘ x) = energy x := by
  unfold energy
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  simp only [Function.comp_apply]
  rw [← f.map_sub, f.norm_map]

theorem energy_ge_eighteen (x : Fin 9 → R3) (hx : x ∈ SphereConfig 9) :
    (18 : ℝ) ≤ energy x := by
  have hpair : ∀ i j : Fin 9, i ≠ j → (1 / 2 : ℝ) ≤ ‖x i - x j‖⁻¹ := by
    intro i j hij
    have hne : x i - x j ≠ 0 := sub_ne_zero.mpr (fun h => hij (hx.2 h))
    have hpos : 0 < ‖x i - x j‖ := norm_pos_iff.mpr hne
    have hle : ‖x i - x j‖ ≤ 2 := by
      calc ‖x i - x j‖ ≤ ‖x i‖ + ‖x j‖ := norm_sub_le _ _
        _ = 2 := by rw [hx.1 i, hx.1 j]; norm_num
    simpa only [one_div] using one_div_le_one_div_of_le hpos hle
  have hconst : (∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, (1 / 2 : ℝ)) = 18 := by
    have hcard : (∑ i : Fin 9, (Finset.Ioi i).card) = 36 := by decide
    have hcardR : (∑ i : Fin 9, ((Finset.Ioi i).card : ℝ)) = 36 := by
      simpa using congrArg (fun n : ℕ => (n : ℝ)) hcard
    calc (∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, (1 / 2 : ℝ))
        = ∑ i : Fin 9, ((Finset.Ioi i).card : ℝ) * (1 / 2) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (∑ i : Fin 9, ((Finset.Ioi i).card : ℝ)) * (1 / 2) := by
          rw [Finset.sum_mul]
      _ = 18 := by rw [hcardR]; norm_num
  calc (18 : ℝ) = ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, (1 / 2 : ℝ) := hconst.symm
    _ ≤ ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, ‖x i - x j‖⁻¹ := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => ?_
        exact hpair i j (ne_of_lt (Finset.mem_Ioi.mp hj))
    _ = energy x := rfl

theorem hasDerivAt_energy_candidate (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt (fun s : ℝ => energy (candidate s)) (familyEnergyDeriv r) r := by
  have hfun : (fun s : ℝ => energy (candidate s)) =ᶠ[nhds r] familyEnergy := by
    filter_upwards [Ioo_mem_nhds hr hr1] with s hs
    exact energy_candidate s hs.1 hs.2
  exact (hasDerivAt_familyEnergy r hr hr1).congr_of_eventuallyEq hfun

theorem sphereConfig_nonempty : (SphereConfig 9).Nonempty :=
  ⟨candidate (1 / 2), candidate_mem_sphere (1 / 2) (by norm_num) (by norm_num)⟩

theorem norm_sub_sq_eq_inner (x : Fin 9 → R3) (hx : x ∈ SphereConfig 9) (i j : Fin 9) :
    ‖x i - x j‖ ^ 2 = 2 - 2 * ⟪x i, x j⟫_ℝ := by
  rw [norm_sub_sq_real, hx.1 i, hx.1 j]
  ring

theorem norm_sub_eq_sqrt_inner (x : Fin 9 → R3) (hx : x ∈ SphereConfig 9) (i j : Fin 9) :
    ‖x i - x j‖ = Real.sqrt (2 - 2 * ⟪x i, x j⟫_ℝ) := by
  rw [← Real.sqrt_sq (norm_nonneg _), norm_sub_sq_eq_inner x hx i j]

theorem energy_eq_inner (x : Fin 9 → R3) (hx : x ∈ SphereConfig 9) :
    energy x =
      ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, (Real.sqrt (2 - 2 * ⟪x i, x j⟫_ℝ))⁻¹ := by
  unfold energy
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [norm_sub_eq_sqrt_inner x hx i j]

theorem sphereConfig_comp_isometry (x : Fin 9 → R3) (f : R3 ≃ₗᵢ[ℝ] R3)
    (hx : x ∈ SphereConfig 9) : (f ∘ x) ∈ SphereConfig 9 := by
  constructor
  · intro i
    change ‖f (x i)‖ = 1
    rw [f.norm_map, hx.1 i]
  · exact f.injective.comp hx.2

end ThomsonNine
