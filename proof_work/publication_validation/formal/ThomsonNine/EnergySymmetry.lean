import ThomsonNine.EnergyPath
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open scoped BigOperators InnerProductSpace
namespace ThomsonNine

/-- Twice the energy is the symmetric double sum over all ordered pairs. -/
theorem two_mul_energy (x : Fin 9 → R3) :
    2 * energy x =
      ∑ i : Fin 9, ∑ j : Fin 9, (if j = i then 0 else ‖x i - x j‖⁻¹) := by
  unfold energy
  have h1 : ∀ i : Fin 9, (∑ j : Fin 9, (if j = i then 0 else ‖x i - x j‖⁻¹))
      = (∑ j ∈ Finset.Iio i, ‖x i - x j‖⁻¹)
        + (∑ j ∈ Finset.Ioi i, ‖x i - x j‖⁻¹) := by
    intro i
    rw [sum_univ_ite_eq_sum_erase (fun j => ‖x i - x j‖⁻¹) i]
    exact sum_erase_eq_sum_Iio_add_Ioi (fun j => ‖x i - x j‖⁻¹) i
  simp only [h1]
  rw [Finset.sum_add_distrib]
  have hfirst : (∑ i : Fin 9, ∑ j ∈ Finset.Iio i, ‖x i - x j‖⁻¹)
      = ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, ‖x i - x j‖⁻¹ := by
    rw [sum_Iio_swap (fun i j => ‖x i - x j‖⁻¹)]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [norm_sub_rev]
  rw [hfirst]
  ring

/-- The energy is invariant under relabeling the nine points. -/
theorem energy_perm (σ : Equiv.Perm (Fin 9)) (x : Fin 9 → R3) :
    energy (fun i => x (σ i)) = energy x := by
  have h2 := two_mul_energy (fun i => x (σ i))
  have h1 := two_mul_energy x
  have hreindex : (∑ i : Fin 9, ∑ j : Fin 9,
        (if j = i then 0 else ‖x (σ i) - x (σ j)‖⁻¹))
      = ∑ i : Fin 9, ∑ j : Fin 9, (if j = i then 0 else ‖x i - x j‖⁻¹) := by
    rw [← Equiv.sum_comp σ
      (fun i => ∑ j : Fin 9, (if j = i then 0 else ‖x i - x j‖⁻¹))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Equiv.sum_comp σ
      (fun j => (if j = σ i then 0 else ‖x (σ i) - x j‖⁻¹))]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [σ.injective.eq_iff]
  rw [hreindex] at h2
  linarith

/-- Relabeling preserves membership in the sphere configuration set. -/
theorem sphereConfig_perm (σ : Equiv.Perm (Fin 9)) {x : Fin 9 → R3}
    (hx : x ∈ SphereConfig 9) : (fun i => x (σ i)) ∈ SphereConfig 9 := by
  refine ⟨fun i => hx.1 (σ i), ?_⟩
  intro i j hij
  exact σ.injective (hx.2 hij)

end ThomsonNine
