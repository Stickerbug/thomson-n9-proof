import ThomsonNine.EnergyPath
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open scoped BigOperators InnerProductSpace
namespace ThomsonNine

/-- The gradient vanishes at every point iff all directional derivatives vanish. -/
theorem gradient_zero_iff_directional (x : Fin 9 → R3) :
    (∀ i, gradAt x i = 0) ↔ ∀ v : Fin 9 → R3, (∑ i, ⟪v i, gradAt x i⟫_ℝ) = 0 := by
  constructor
  · intro h v
    simp [h]
  · intro h i
    have hv := h (fun j => if j = i then gradAt x i else 0)
    have hsingle : (∑ j : Fin 9, ⟪(if j = i then gradAt x i else 0), gradAt x j⟫_ℝ)
        = ⟪gradAt x i, gradAt x i⟫_ℝ := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [hji]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    rw [hsingle, real_inner_self_eq_norm_sq] at hv
    have h0 : ‖gradAt x i‖ = 0 := by
      nlinarith [norm_nonneg (gradAt x i)]
    exact norm_eq_zero.mp h0

/-- Vanishing gradient gives vanishing multi-point energy derivative. -/
theorem hasDerivAt_energy_path_zero (x : Fin 9 → R3) (hx : Function.Injective x)
    (hgrad : ∀ i, gradAt x i = 0) (v : Fin 9 → R3) :
    HasDerivAt (fun t : ℝ => energy (fun i => x i + t • v i)) 0 0 := by
  simpa only [hgrad, inner_zero_right, Finset.sum_const_zero] using
    hasDerivAt_energy_path x hx v

/-- Stationarity is equivalent to vanishing of the gradient. -/
theorem stationary_iff_gradient_zero (x : Fin 9 → R3) (hx : Function.Injective x) :
    (∀ v : Fin 9 → R3,
        HasDerivAt (fun t : ℝ => energy (fun i => x i + t • v i)) 0 0) ↔
      ∀ i, gradAt x i = 0 := by
  constructor
  · intro hstat
    rw [gradient_zero_iff_directional]
    intro v
    have h := (hstat v).unique (hasDerivAt_energy_path x hx v)
    exact h.symm
  · intro hgrad v
    exact hasDerivAt_energy_path_zero x hx hgrad v

end ThomsonNine
