import ThomsonNine.Statement
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.GroupWithZero

open ThomsonNine
open scoped BigOperators

namespace ThomsonNine

/-! Continuity of the nine-point Coulomb energy on injective configurations.

This is a foundational analytic lemma: every pair term is continuous as long as the
two points do not collide. -/

theorem continuousAt_energy_of_injective (x : Fin 9 → R3) (hx : Function.Injective x) :
    ContinuousAt (energy : (Fin 9 → R3) → ℝ) x := by
  have hpair : ∀ i j : Fin 9, x i ≠ x j →
      ContinuousAt (fun y : Fin 9 → R3 => ‖y i - y j‖⁻¹) x := by
    intro i j hij
    have hsub : Continuous (fun y : Fin 9 → R3 => y i - y j) :=
      (continuous_apply i).sub (continuous_apply j)
    have hnorm : ContinuousAt (fun y : Fin 9 → R3 => ‖y i - y j‖) x :=
      (continuous_norm.comp hsub).continuousAt
    exact hnorm.inv₀ (by simpa [norm_eq_zero] using (sub_ne_zero.mpr hij))
  change ContinuousAt
    (fun y : Fin 9 → R3 => ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, ‖y i - y j‖⁻¹) x
  refine tendsto_finsetSum (Finset.univ : Finset (Fin 9)) ?_
  intro i _
  refine tendsto_finsetSum (Finset.Ioi i) ?_
  intro j hj
  have hlt : i < j := Finset.mem_Ioi.mp hj
  exact hpair i j (fun heq => (ne_of_lt hlt) (hx heq))

theorem continuousOn_energy_injective :
    ContinuousOn (energy : (Fin 9 → R3) → ℝ) {x | Function.Injective x} := by
  intro x hx
  exact (continuousAt_energy_of_injective x hx).continuousWithinAt

end ThomsonNine
