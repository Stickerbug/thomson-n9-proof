/-
Two structural forms of the Coulomb energy.

* `energy_smul`: the energy is homogeneous of degree `-1`, i.e.
  `energy (c • x) = c⁻¹ * energy x` for `c > 0`; equivalently, scaling all
  points by `1 + t` differentiates to `-energy x` at `t = 0`
  (`hasDerivAt_energy_scale`).
* `energy_eq_sum_rpow`: for a nine-point unit configuration the energy is the
  sum of `f (⟪x i, x j⟫)` with `f t = (2 - 2 t) ^ (-(1/2))`, matching the
  three-variable reduction used in the proof candidate.

No `sorry` or `axiom` is used.
-/
import ThomsonNine.Applications
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

open scoped BigOperators InnerProductSpace
open Filter

namespace ThomsonNine

/-! ### Homogeneity of degree `-1` -/

theorem energy_smul (c : ℝ) (hc : 0 < c) (x : Fin 9 → R3) :
    energy (fun i => c • x i) = c⁻¹ * energy x := by
  unfold energy
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg hc.le, mul_inv]

/-- Scaling all nine points by `1 + t` differentiates to `-energy x` at
`t = 0`. -/
theorem hasDerivAt_energy_scale (x : Fin 9 → R3) :
    HasDerivAt (fun t : ℝ => energy (fun i => (1 + t) • x i)) (- energy x) 0 := by
  have hlin : HasDerivAt (fun t : ℝ => (1 + t)) 1 0 :=
    (hasDerivAt_id (0 : ℝ)).const_add 1
  have hinv : HasDerivAt (fun t : ℝ => (1 + t)⁻¹) (-1) 0 := by
    have h := hlin.inv (by norm_num : (1 + (0 : ℝ)) ≠ 0)
    convert h using 1
    norm_num
  have hmul : HasDerivAt (fun t : ℝ => (1 + t)⁻¹ * energy x) (-1 * energy x) 0 :=
    hinv.mul_const (energy x)
  have hev : (fun t : ℝ => (1 + t)⁻¹ * energy x) =ᶠ[nhds (0 : ℝ)]
      fun t : ℝ => energy (fun i => (1 + t) • x i) := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)]
      with t ht
    have hpos : 0 < 1 + t := by linarith [ht.1]
    exact (energy_smul (1 + t) hpos x).symm
  have := hmul.congr_of_eventuallyEq hev.symm
  simpa using this

/-! ### The `f t = (2 - 2 t) ^ (-(1/2))` form -/

theorem energy_eq_sum_rpow (x : Fin 9 → R3) (hx : x ∈ SphereConfig 9) :
    energy x =
      ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, (2 - 2 * ⟪x i, x j⟫_ℝ) ^ (-(1 / 2) : ℝ) := by
  rw [energy_eq_inner x hx]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hnn : (0 : ℝ) ≤ 2 - 2 * ⟪x i, x j⟫_ℝ := by
    have h := norm_sub_sq_eq_inner x hx i j
    nlinarith [sq_nonneg ‖x i - x j‖]
  rw [Real.sqrt_eq_rpow]
  exact (Real.rpow_neg hnn (1 / 2)).symm

end ThomsonNine
