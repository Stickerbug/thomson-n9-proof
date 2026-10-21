import ThomsonNine.GradientZero
import ThomsonNine.EnergyBounds
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open scoped BigOperators InnerProductSpace
open Filter
namespace ThomsonNine

/-- An energy upper bound forces a quantitative upper bound on every inner product. -/
theorem inner_le_of_energy_le {x : Fin 9 → R3} (hx : x ∈ SphereConfig 9)
    {U : ℝ} (hU : 0 < U) (hE : energy x ≤ U) {i j : Fin 9} (hij : i ≠ j) :
    ⟪x i, x j⟫_ℝ ≤ 1 - (U ^ 2)⁻¹ / 2 := by
  have hd := dist_ge_inv_energy hx hU hE hij
  have hUinv : (0:ℝ) < U⁻¹ := inv_pos.mpr hU
  have hsq : (U⁻¹) ^ 2 ≤ ‖x i - x j‖ ^ 2 := pow_le_pow_left₀ hUinv.le hd 2
  rw [norm_sub_sq_eq_inner x hx i j] at hsq
  have h2 : (U⁻¹) ^ 2 = (U ^ 2)⁻¹ := by rw [inv_pow]
  rw [h2] at hsq
  have hmain : 2 * ⟪x i, x j⟫_ℝ + (U ^ 2)⁻¹ ≤ 2 := by linarith
  linarith

/-- Local minimality along every affine path forces the gradient to vanish. -/
theorem local_min_gradient_zero (x : Fin 9 → R3) (hx : Function.Injective x)
    (hmin : ∀ v : Fin 9 → R3,
      IsLocalMin (fun t : ℝ => energy (fun i => x i + t • v i)) 0) :
    ∀ i, gradAt x i = 0 := by
  refine (stationary_iff_gradient_zero x hx).mp ?_
  intro v
  have hzero := (hmin v).hasDerivAt_eq_zero (hasDerivAt_energy_path x hx v)
  simpa only [hzero] using hasDerivAt_energy_path x hx v

/-- A local minimum of the energy in the ambient space has vanishing gradient. -/
theorem isLocalMin_gradient_zero (x : Fin 9 → R3) (hx : Function.Injective x)
    (hmin : IsLocalMin energy x) : ∀ i, gradAt x i = 0 := by
  apply local_min_gradient_zero x hx
  intro v
  have hcont : Continuous (fun t : ℝ => (fun i : Fin 9 => x i + t • v i)) := by
    continuity
  have hpt : (fun i : Fin 9 => x i + (0:ℝ) • v i) = x := by
    funext i; simp
  have ht : Tendsto (fun t : ℝ => (fun i : Fin 9 => x i + t • v i)) (nhds (0:ℝ)) (nhds x) := by
    simpa only [hpt] using hcont.tendsto 0
  have hev := ht.eventually hmin
  change ∀ᶠ t in nhds (0:ℝ),
    energy (fun i => x i + (0:ℝ) • v i) ≤ energy (fun i => x i + t • v i)
  rw [hpt]
  exact hev

end ThomsonNine
