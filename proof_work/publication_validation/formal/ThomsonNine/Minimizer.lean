import ThomsonNine.EnergyValue
import ThomsonNine.EnergyBounds
import ThomsonNine.EnergyContinuity
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open scoped BigOperators InnerProductSpace
open Metric

namespace ThomsonNine

open ThomsonNine.Family

/-- The compact "shell" of configurations whose pairwise distances are bounded below
by `1/26`.  Every configuration of energy at most `26` lies in this shell, and the
shell is closed and bounded, hence compact. -/
def feasibleShell : Set (Fin 9 → R3) :=
  {x | (∀ i, ‖x i‖ = 1) ∧ ∀ i j : Fin 9, i ≠ j → (1 / 26 : ℝ) ≤ ‖x i - x j‖}

lemma feasibleShell_subset_pi :
    feasibleShell ⊆ Set.pi Set.univ (fun _ : Fin 9 => Metric.sphere (0 : R3) 1) := by
  intro x hx i _
  rw [Metric.mem_sphere, dist_eq_norm]
  simpa using hx.1 i

lemma feasibleShell_eq_inter :
    feasibleShell = (⋂ i : Fin 9, {x : Fin 9 → R3 | ‖x i‖ = 1}) ∩
      (⋂ i : Fin 9, ⋂ j : Fin 9,
        if i = j then (Set.univ : Set (Fin 9 → R3))
        else {x : Fin 9 → R3 | (1 / 26 : ℝ) ≤ ‖x i - x j‖}) := by
  ext x
  simp only [feasibleShell, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun i j => ?_⟩
    by_cases h : i = j
    · rw [if_pos h]
      exact Set.mem_univ x
    · rw [if_neg h]
      exact h2 i j h
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun i j hij => ?_⟩
    have h2' := h2 i j
    by_cases h : i = j
    · exact absurd h hij
    · rw [if_neg h] at h2'
      exact h2'

lemma isClosed_feasibleShell : IsClosed feasibleShell := by
  rw [feasibleShell_eq_inter]
  refine IsClosed.inter ?_ ?_
  · exact isClosed_iInter (fun i =>
      isClosed_eq (continuous_norm.comp (continuous_apply i)) continuous_const)
  · refine isClosed_iInter (fun i => isClosed_iInter (fun j => ?_))
    by_cases h : i = j
    · rw [if_pos h]
      exact isClosed_univ
    · rw [if_neg h]
      exact isClosed_le continuous_const
        (continuous_norm.comp ((continuous_apply i).sub (continuous_apply j)))

lemma isCompact_feasibleShell : IsCompact feasibleShell := by
  have hcomp : IsCompact (Set.pi Set.univ (fun _ : Fin 9 => Metric.sphere (0 : R3) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_sphere (0 : R3) 1)
  exact hcomp.of_isClosed_subset isClosed_feasibleShell feasibleShell_subset_pi

lemma feasibleShell_nonempty : feasibleShell.Nonempty := by
  obtain ⟨r, hr, hr1, hz, hlt⟩ := exists_candidate_energy_lt_26
  have hmem := candidate_mem_sphere r hr hr1
  exact ⟨candidate r, fun i => hmem.1 i, fun i j hij =>
    by simpa [one_div] using dist_ge_inv_energy hmem (by norm_num : (0 : ℝ) < 26) hlt.le hij⟩

lemma continuousOn_energy_feasibleShell : ContinuousOn energy feasibleShell := by
  intro x hx
  have hinj : Function.Injective x := by
    intro i j hij
    by_contra hne
    have hpos := hx.2 i j hne
    rw [hij, sub_self, norm_zero] at hpos
    linarith
  exact (continuousAt_energy_of_injective x hinj).continuousWithinAt

theorem exists_isMinOn_energy_feasibleShell :
    ∃ x ∈ feasibleShell, ∀ y ∈ feasibleShell, energy x ≤ energy y :=
  isCompact_feasibleShell.exists_isMinOn feasibleShell_nonempty continuousOn_energy_feasibleShell

/-- The nine-point Thomson energy attains its global minimum on `SphereConfig 9`:
there is an admissible configuration whose energy is at most that of every other
admissible configuration. -/
theorem exists_global_minimizer :
    ∃ x : Fin 9 → R3, x ∈ SphereConfig 9 ∧ ∀ y ∈ SphereConfig 9, energy x ≤ energy y := by
  obtain ⟨x0, hx0, hmin⟩ := exists_isMinOn_energy_feasibleShell
  have hx0inj : Function.Injective x0 := by
    intro i j hij
    by_contra hne
    have hpos := hx0.2 i j hne
    rw [hij, sub_self, norm_zero] at hpos
    linarith
  refine ⟨x0, ⟨hx0.1, hx0inj⟩, ?_⟩
  intro y hy
  by_cases hE : energy y ≤ 26
  · exact hmin y ⟨hy.1, fun i j hij =>
      by simpa [one_div] using dist_ge_inv_energy hy (by norm_num : (0 : ℝ) < 26) hE hij⟩
  · have hE' : (26 : ℝ) < energy y := lt_of_not_ge hE
    obtain ⟨r, hr, hr1, hz, hlt⟩ := exists_candidate_energy_lt_26
    have hmem := candidate_mem_sphere r hr hr1
    have hcand : candidate r ∈ feasibleShell :=
      ⟨fun i => hmem.1 i, fun i j hij =>
        by simpa [one_div] using dist_ge_inv_energy hmem (by norm_num : (0 : ℝ) < 26) hlt.le hij⟩
    have hle := hmin (candidate r) hcand
    linarith

theorem exists_global_minimizer_lt_26 :
    ∃ x : Fin 9 → R3, x ∈ SphereConfig 9 ∧
      (∀ y ∈ SphereConfig 9, energy x ≤ energy y) ∧ energy x < 26 := by
  obtain ⟨x0, hx0, hmin⟩ := exists_global_minimizer
  obtain ⟨r, hr, hr1, hz, hlt⟩ := exists_candidate_energy_lt_26
  have hmem := candidate_mem_sphere r hr hr1
  exact ⟨x0, hx0, hmin, lt_of_le_of_lt (hmin (candidate r) hmem) hlt⟩

end ThomsonNine
