import ThomsonNine.EnergyBounds

open scoped BigOperators InnerProductSpace
open ThomsonNine

namespace ThomsonNine
open ThomsonNine.Family

/-! Exact pairwise distances of the one-parameter candidate family.

The 36 reciprocal-distance lemmas in `Family.lean` are converted into exact
distance equalities; the six representative values are
`√3 r`, `2√(1-r²)`, `√(4-r²)`, `√3`, `√(2-r)` and `√(2+2r)`.  The last two
theorems connect distances with the inner-product form of the energy. -/

theorem dist_p_T_T (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 0 - p r 1‖ = Real.sqrt 3 * r := by
  simpa using congrArg (fun x : ℝ => x⁻¹) (d01 r hr hr1)

theorem dist_p_T_B_same (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 0 - p r 3‖ = 2 * Real.sqrt (1 - r ^ 2) := by
  simpa using congrArg (fun x : ℝ => x⁻¹) (d03 r hr hr1)

theorem dist_p_T_B_diff (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 0 - p r 4‖ = Real.sqrt (4 - r ^ 2) := by
  simpa using congrArg (fun x : ℝ => x⁻¹) (d04 r hr hr1)

theorem dist_p_E_E (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 6 - p r 7‖ = Real.sqrt 3 := by
  simpa using congrArg (fun x : ℝ => x⁻¹) (d67 r hr hr1)

theorem dist_p_T_E_near (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 0 - p r 6‖ = Real.sqrt (2 - r) := by
  simpa using congrArg (fun x : ℝ => x⁻¹) (d06 r hr hr1)

theorem dist_p_T_E_far (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 0 - p r 7‖ = Real.sqrt (2 + 2 * r) := by
  simpa using congrArg (fun x : ℝ => x⁻¹) (d07 r hr hr1)

theorem dist_p_T_E_far_B (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 3 - p r 7‖ = Real.sqrt (2 + 2 * r) := by
  simpa using congrArg (fun x : ℝ => x⁻¹) (d37 r hr hr1)

theorem dist_candidate_eq_sqrt_inner (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i j : Fin 9) :
    ‖candidate r i - candidate r j‖ =
      Real.sqrt (2 - 2 * ⟪candidate r i, candidate r j⟫_ℝ) :=
  norm_sub_eq_sqrt_inner _ (candidate_mem_sphere r hr hr1) i j

theorem dist_sq_candidate_eq_inner (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i j : Fin 9) :
    ‖candidate r i - candidate r j‖ ^ 2 =
      2 - 2 * ⟪candidate r i, candidate r j⟫_ℝ :=
  norm_sub_sq_eq_inner _ (candidate_mem_sphere r hr hr1) i j

end ThomsonNine
