import ThomsonNine.Applications
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open scoped BigOperators InnerProductSpace
namespace ThomsonNine

/-- The straight path `t ↦ x + t • v` has derivative `v` at `0`. -/
theorem hasDerivAt_affine (x v : R3) :
    HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
  have h : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  simpa using h.const_add x

/-- Derivative of the squared distance `‖x + t v‖²` along a straight path. -/
theorem hasDerivAt_norm_sq_affine (x v : R3) :
    HasDerivAt (fun t : ℝ => ‖x + t • v‖ ^ 2) (2 * ⟪x, v⟫_ℝ) 0 := by
  have h := (hasDerivAt_affine x v).norm_sq
  simpa using h


/-- Derivative of the norm `‖x + t v‖` along a straight path. -/
theorem hasDerivAt_norm_affine (x v : R3) (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => ‖x + t • v‖) (⟪x, v⟫_ℝ / ‖x‖) 0 := by
  have hf : HasDerivAt (fun t : ℝ => ‖x + t • v‖ ^ 2) (2 * ⟪x, v⟫_ℝ) 0 :=
    hasDerivAt_norm_sq_affine x v
  have hxpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  have hsq : (fun t : ℝ => ‖x + t • v‖ ^ 2) 0 ≠ 0 := by
    simp only [zero_smul, add_zero]
    exact pow_ne_zero 2 hxpos.ne'
  have h := hf.sqrt hsq
  convert h using 1
  · funext t
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  · simp only [zero_smul, add_zero]
    rw [Real.sqrt_sq hxpos.le]
    field_simp

/-- Derivative of the inverse distance `‖x + t v‖⁻¹` along a straight path. -/
theorem hasDerivAt_inv_norm_affine (x v : R3) (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => ‖x + t • v‖⁻¹) (-(⟪x, v⟫_ℝ) / ‖x‖ ^ 3) 0 := by
  have hxpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  have hn := hasDerivAt_norm_affine x v hx
  have h0 : (fun t : ℝ => ‖x + t • v‖) 0 ≠ 0 := by
    simpa using hxpos.ne'
  have hinv := hn.inv h0
  convert hinv using 1
  simp only [zero_smul, add_zero]
  field_simp

end ThomsonNine
