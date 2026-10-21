import ThomsonNine.Applications
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators
open ThomsonNine

namespace ThomsonNine
open ThomsonNine.Family

/-! Energy bounds and the first step of the pair reduction.

The energy of nine points on the unit sphere is at least `18`.  Conversely, if
the energy is at most `U`, every one of the 36 pair distances is at least
`U⁻¹`; together with the trivial diameter bound this confines each distance to
an interval.  The last theorem transfers the strict family minimum to the
energies of the actual candidate configurations on the sphere. -/

theorem dist_le_two (x : Fin 9 → R3) (hx : x ∈ SphereConfig 9) (i j : Fin 9) :
    ‖x i - x j‖ ≤ 2 := by
  calc ‖x i - x j‖ ≤ ‖x i‖ + ‖x j‖ := norm_sub_le _ _
    _ = 2 := by rw [hx.1 i, hx.1 j]; norm_num

theorem inv_dist_le_energy_of_lt {i j : Fin 9} (h : i < j) (x : Fin 9 → R3) :
    ‖x i - x j‖⁻¹ ≤ energy x := by
  have hmem : j ∈ Finset.Ioi i := Finset.mem_Ioi.mpr h
  have hinner : ‖x i - x j‖⁻¹ ≤ ∑ b ∈ Finset.Ioi i, ‖x i - x b‖⁻¹ :=
    Finset.single_le_sum (f := fun b => ‖x i - x b‖⁻¹)
      (by intro b _; exact inv_nonneg.mpr (norm_nonneg _)) hmem
  have houter : (∑ b ∈ Finset.Ioi i, ‖x i - x b‖⁻¹) ≤ energy x := by
    unfold energy
    exact Finset.single_le_sum (f := fun a => ∑ b ∈ Finset.Ioi a, ‖x a - x b‖⁻¹)
      (by intro a _; exact Finset.sum_nonneg (by intro b _; exact inv_nonneg.mpr (norm_nonneg _)))
      (Finset.mem_univ i)
  exact hinner.trans houter

theorem inv_dist_le_energy {i j : Fin 9} (hij : i ≠ j) (x : Fin 9 → R3) :
    ‖x i - x j‖⁻¹ ≤ energy x := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact inv_dist_le_energy_of_lt h x
  · rw [norm_sub_rev]
    exact inv_dist_le_energy_of_lt h x

theorem dist_ge_inv_energy {x : Fin 9 → R3} (hx : x ∈ SphereConfig 9)
    {U : ℝ} (hU : 0 < U) (hE : energy x ≤ U) {i j : Fin 9} (hij : i ≠ j) :
    U⁻¹ ≤ ‖x i - x j‖ := by
  have hd : 0 < ‖x i - x j‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hij (hx.2 h)))
  have h1 : ‖x i - x j‖⁻¹ ≤ U := (inv_dist_le_energy hij x).trans hE
  exact (inv_le_comm₀ hU hd).mpr h1

theorem energy_candidate_strict_min (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hz : familyEnergyDeriv r = 0) :
    ∀ s, 0 < s → s < 1 → s ≠ r → energy (candidate r) < energy (candidate s) := by
  intro s hs hs1 hne
  rw [energy_candidate r hr hr1, energy_candidate s hs hs1]
  exact familyEnergy_min r hr hr1 hz s hs hs1 hne

theorem exists_candidate_strict_energy_min :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ familyEnergyDeriv r = 0 ∧
      ∀ s, 0 < s → s < 1 → s ≠ r → energy (candidate r) < energy (candidate s) := by
  obtain ⟨r, hrI, hz⟩ := exists_familyEnergyDeriv_zero
  have hr : 0 < r := by linarith [hrI.1]
  have hr1 : r < 1 := by linarith [hrI.2]
  exact ⟨r, hr, hr1, hz, energy_candidate_strict_min r hr hr1 hz⟩

end ThomsonNine
