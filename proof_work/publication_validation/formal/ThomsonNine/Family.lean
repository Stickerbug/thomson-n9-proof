import ThomsonNine.Statement
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped BigOperators
open Real

namespace ThomsonNine
namespace Family

/-! Explicit coordinates for the candidate configuration. -/

noncomputable def p (r : ℝ) : Fin 9 → R3 :=
  ![cyl r 0 (Real.sqrt (1 - r ^ 2)),
    cyl r (2 * π / 3) (Real.sqrt (1 - r ^ 2)),
    cyl r (4 * π / 3) (Real.sqrt (1 - r ^ 2)),
    cyl r 0 (-Real.sqrt (1 - r ^ 2)),
    cyl r (2 * π / 3) (-Real.sqrt (1 - r ^ 2)),
    cyl r (4 * π / 3) (-Real.sqrt (1 - r ^ 2)),
    cyl 1 (π / 3) 0, cyl 1 π 0, cyl 1 (5 * π / 3) 0]

lemma sqdist_cyl (ρ₁ θ₁ h₁ ρ₂ θ₂ h₂ : ℝ) :
    ‖cyl ρ₁ θ₁ h₁ - cyl ρ₂ θ₂ h₂‖ ^ 2 =
      (ρ₁ * Real.cos θ₁ - ρ₂ * Real.cos θ₂) ^ 2 +
      (ρ₁ * Real.sin θ₁ - ρ₂ * Real.sin θ₂) ^ 2 + (h₁ - h₂) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [cyl, Fin.sum_univ_three]

lemma norm_cyl_sq (ρ θ h : ℝ) : ‖cyl ρ θ h‖ ^ 2 = ρ ^ 2 + h ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [cyl, Fin.sum_univ_three]
  ring_nf
  nlinarith [Real.sin_sq_add_cos_sq θ]

lemma cos_two_pi_div_three : Real.cos (2 * π / 3) = -1 / 2 := by
  have h : 2 * π / 3 = π / 3 + π / 3 := by ring
  rw [h, Real.cos_add, Real.cos_pi_div_three, Real.sin_pi_div_three]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

lemma sin_two_pi_div_three : Real.sin (2 * π / 3) = Real.sqrt 3 / 2 := by
  have h : 2 * π / 3 = π / 3 + π / 3 := by ring
  rw [h, Real.sin_add, Real.cos_pi_div_three, Real.sin_pi_div_three]
  ring_nf

lemma cos_four_pi_div_three : Real.cos (4 * π / 3) = -1 / 2 := by
  have h : 4 * π / 3 = π / 3 + π := by ring
  rw [h, Real.cos_add_pi, Real.cos_pi_div_three]
  norm_num

lemma sin_four_pi_div_three : Real.sin (4 * π / 3) = -Real.sqrt 3 / 2 := by
  have h : 4 * π / 3 = π / 3 + π := by ring
  rw [h, Real.sin_add_pi, Real.sin_pi_div_three]
  ring

lemma cos_five_pi_div_three : Real.cos (5 * π / 3) = 1 / 2 := by
  have h : 5 * π / 3 = 2 * π - π / 3 := by ring
  rw [h, Real.cos_two_pi_sub, Real.cos_pi_div_three]

lemma sin_five_pi_div_three : Real.sin (5 * π / 3) = -Real.sqrt 3 / 2 := by
  have h : 5 * π / 3 = 2 * π - π / 3 := by ring
  rw [h, Real.sin_two_pi_sub, Real.sin_pi_div_three]
  ring

lemma inv_eq_of_sq_eq_sq {h₀ d : ℝ} (hh : 0 ≤ h₀) (hd : 0 < d)
    (hsq : h₀ ^ 2 = d ^ 2) : h₀⁻¹ = d⁻¹ := by
  have h2 : h₀ = d := by
    have hprod : (h₀ - d) * (h₀ + d) = 0 := by nlinarith [hsq]
    rcases mul_eq_zero.mp hprod with h | h
    · linarith
    · linarith
  rw [h2]

lemma pos_T {r : ℝ} (hr : 0 < r) (hr1 : r < 1) : 0 < Real.sqrt 3 * r := by
  positivity

lemma pos_S {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    0 < 2 * Real.sqrt (1 - r ^ 2) := by
  have h : 0 < 1 - r ^ 2 := by nlinarith [mul_pos hr (sub_pos.mpr hr1)]
  have h2 : 0 < Real.sqrt (1 - r ^ 2) := Real.sqrt_pos.mpr h
  positivity

lemma pos_U {r : ℝ} (hr : 0 < r) (hr1 : r < 1) : 0 < Real.sqrt (4 - r ^ 2) := by
  apply Real.sqrt_pos.mpr
  nlinarith [mul_pos hr (sub_pos.mpr hr1)]

lemma pos_E3 {r : ℝ} (hr : 0 < r) (hr1 : r < 1) : 0 < Real.sqrt 3 := by
  positivity

lemma pos_V {r : ℝ} (hr : 0 < r) (hr1 : r < 1) : 0 < Real.sqrt (2 - r) := by
  apply Real.sqrt_pos.mpr
  linarith

lemma pos_W {r : ℝ} (hr : 0 < r) (hr1 : r < 1) : 0 < Real.sqrt (2 + 2 * r) := by
  apply Real.sqrt_pos.mpr
  positivity

lemma sqrt3_div_r {r : ℝ} (hr : 0 < r) :
    2 * Real.sqrt 3 / r = 6 * (Real.sqrt 3 * r)⁻¹ := by
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  have hr0 : r ≠ 0 := ne_of_gt hr
  rw [show (6 * (Real.sqrt 3 * r)⁻¹) = (6 : ℝ) / (Real.sqrt 3 * r) by rw [div_eq_mul_inv]]
  rw [show (2 * Real.sqrt 3 / r) = (2 * Real.sqrt 3) / r by rfl]
  rw [div_eq_div_iff hr0 (mul_ne_zero h3 hr0)]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  ring

lemma sqrt3_eq_inv : Real.sqrt 3 = 3 * (Real.sqrt 3)⁻¹ := by
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  rw [show (3 * (Real.sqrt 3)⁻¹) = (3 : ℝ) / Real.sqrt 3 by rw [div_eq_mul_inv]]
  rw [eq_div_iff h3]
  rw [← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

lemma d01 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 0 - p r 1‖⁻¹ = (Real.sqrt 3 * r)⁻¹ := by
  have hsq : ‖p r 0 - p r 1‖ ^ 2 = (Real.sqrt 3 * r) ^ 2 := by
    simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three,
      cos_four_pi_div_three, sin_four_pi_div_three, cos_five_pi_div_three,
      sin_five_pi_div_three, cos_pi_div_three, sin_pi_div_three]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
    try rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
    ring_nf
    try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_T hr hr1) hsq

lemma d02 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 0 - p r 2‖⁻¹ = (Real.sqrt 3 * r)⁻¹ := by
  have hsq : ‖p r 0 - p r 2‖ ^ 2 = (Real.sqrt 3 * r) ^ 2 := by
    simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three,
      cos_four_pi_div_three, sin_four_pi_div_three, cos_five_pi_div_three,
      sin_five_pi_div_three, cos_pi_div_three, sin_pi_div_three]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
    try rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
    ring_nf
    try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_T hr hr1) hsq

lemma d03 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 0 - p r 3‖⁻¹ = (2 * Real.sqrt (1 - r ^ 2))⁻¹ := by
  have hsq : ‖p r 0 - p r 3‖ ^ 2 = (2 * Real.sqrt (1 - r ^ 2)) ^ 2 := by
    simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three,
      cos_four_pi_div_three, sin_four_pi_div_three, cos_five_pi_div_three,
      sin_five_pi_div_three, cos_pi_div_three, sin_pi_div_three]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
    try rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
    ring_nf
    try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_S hr hr1) hsq

lemma d04 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 0 - p r 4‖⁻¹ = (Real.sqrt (4 - r ^ 2))⁻¹ := by
  have hsq : ‖p r 0 - p r 4‖ ^ 2 = (Real.sqrt (4 - r ^ 2)) ^ 2 := by
    simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three,
      cos_four_pi_div_three, sin_four_pi_div_three, cos_five_pi_div_three,
      sin_five_pi_div_three, cos_pi_div_three, sin_pi_div_three]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
    try rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
    ring_nf
    try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_U hr hr1) hsq

lemma d05 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 0 - p r 5‖⁻¹ = (Real.sqrt (4 - r ^ 2))⁻¹ := by
  have hsq : ‖p r 0 - p r 5‖ ^ 2 = (Real.sqrt (4 - r ^ 2)) ^ 2 := by
    simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three,
      cos_four_pi_div_three, sin_four_pi_div_three, cos_five_pi_div_three,
      sin_five_pi_div_three, cos_pi_div_three, sin_pi_div_three]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
    try rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
    ring_nf
    try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_U hr hr1) hsq

lemma d06 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 0 - p r 6‖⁻¹ = (Real.sqrt (2 - r))⁻¹ := by
  have hsq : ‖p r 0 - p r 6‖ ^ 2 = (Real.sqrt (2 - r)) ^ 2 := by
    simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three,
      cos_four_pi_div_three, sin_four_pi_div_three, cos_five_pi_div_three,
      sin_five_pi_div_three, cos_pi_div_three, sin_pi_div_three]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
    try rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
    ring_nf
    try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_V hr hr1) hsq

lemma d07 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 0 - p r 7‖⁻¹ = (Real.sqrt (2 + 2 * r))⁻¹ := by
  have hsq : ‖p r 0 - p r 7‖ ^ 2 = (Real.sqrt (2 + 2 * r)) ^ 2 := by
    simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three,
      cos_four_pi_div_three, sin_four_pi_div_three, cos_five_pi_div_three,
      sin_five_pi_div_three, cos_pi_div_three, sin_pi_div_three]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
    try rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
    ring_nf
    try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_W hr hr1) hsq

lemma d08 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 0 - p r 8‖⁻¹ = (Real.sqrt (2 - r))⁻¹ := by
  have hsq : ‖p r 0 - p r 8‖ ^ 2 = (Real.sqrt (2 - r)) ^ 2 := by
    simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three,
      cos_four_pi_div_three, sin_four_pi_div_three, cos_five_pi_div_three,
      sin_five_pi_div_three, cos_pi_div_three, sin_pi_div_three]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
    try rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
    ring_nf
    try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_V hr hr1) hsq

lemma d12 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 1 - p r 2‖⁻¹ = (Real.sqrt 3 * r)⁻¹ := by
  have hsq : ‖p r 1 - p r 2‖ ^ 2 = (Real.sqrt 3 * r) ^ 2 := by
    simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three,
      cos_four_pi_div_three, sin_four_pi_div_three, cos_five_pi_div_three,
      sin_five_pi_div_three, cos_pi_div_three, sin_pi_div_three]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
    try rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
    ring_nf
    try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_T hr hr1) hsq

lemma d13 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 1 - p r 3‖⁻¹ = (Real.sqrt (4 - r ^ 2))⁻¹ := by
  have hsq : ‖p r 1 - p r 3‖ ^ 2 = (Real.sqrt (4 - r ^ 2)) ^ 2 := by
    simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three,
      cos_four_pi_div_three, sin_four_pi_div_three, cos_five_pi_div_three,
      sin_five_pi_div_three, cos_pi_div_three, sin_pi_div_three]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
    try rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
    ring_nf
    try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_U hr hr1) hsq

lemma d14 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 1 - p r 4‖⁻¹ = (2 * Real.sqrt (1 - r ^ 2))⁻¹ := by
  have hsq : ‖p r 1 - p r 4‖ ^ 2 = (2 * Real.sqrt (1 - r ^ 2)) ^ 2 := by
    simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three,
      cos_four_pi_div_three, sin_four_pi_div_three, cos_five_pi_div_three,
      sin_five_pi_div_three, cos_pi_div_three, sin_pi_div_three]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
    try rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
    ring_nf
    try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_S hr hr1) hsq

lemma d15 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 1 - p r 5‖⁻¹ = (Real.sqrt (4 - r ^ 2))⁻¹ := by
  have hsq : ‖p r 1 - p r 5‖ ^ 2 = (Real.sqrt (4 - r ^ 2)) ^ 2 := by
    simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three,
      cos_four_pi_div_three, sin_four_pi_div_three, cos_five_pi_div_three,
      sin_five_pi_div_three, cos_pi_div_three, sin_pi_div_three]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
    try rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
    ring_nf
    try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_U hr hr1) hsq

lemma d16 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 1 - p r 6‖⁻¹ = (Real.sqrt (2 - r))⁻¹ := by
  have hsq : ‖p r 1 - p r 6‖ ^ 2 = (Real.sqrt (2 - r)) ^ 2 := by
    simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three,
      cos_four_pi_div_three, sin_four_pi_div_three, cos_five_pi_div_three,
      sin_five_pi_div_three, cos_pi_div_three, sin_pi_div_three]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
    try rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
    ring_nf
    try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_V hr hr1) hsq

lemma d17 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 1 - p r 7‖⁻¹ = (Real.sqrt (2 - r))⁻¹ := by
  have hsq : ‖p r 1 - p r 7‖ ^ 2 = (Real.sqrt (2 - r)) ^ 2 := by
    simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three,
      cos_four_pi_div_three, sin_four_pi_div_three, cos_five_pi_div_three,
      sin_five_pi_div_three, cos_pi_div_three, sin_pi_div_three]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
    try rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
    ring_nf
    try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_V hr hr1) hsq

lemma d18 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 1 - p r 8‖⁻¹ = (Real.sqrt (2 + 2 * r))⁻¹ := by
  have hsq : ‖p r 1 - p r 8‖ ^ 2 = (Real.sqrt (2 + 2 * r)) ^ 2 := by
    simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three,
      cos_four_pi_div_three, sin_four_pi_div_three, cos_five_pi_div_three,
      sin_five_pi_div_three, cos_pi_div_three, sin_pi_div_three]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
    try rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
    ring_nf
    try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_W hr hr1) hsq

lemma d23 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 2 - p r 3‖⁻¹ = (Real.sqrt (4 - r ^ 2))⁻¹ := by
  have hsq : ‖p r 2 - p r 3‖ ^ 2 = (Real.sqrt (4 - r ^ 2)) ^ 2 := by
    simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three,
      cos_four_pi_div_three, sin_four_pi_div_three, cos_five_pi_div_three,
      sin_five_pi_div_three, cos_pi_div_three, sin_pi_div_three]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
    try rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
    ring_nf
    try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_U hr hr1) hsq

lemma d24 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 2 - p r 4‖⁻¹ = (Real.sqrt (4 - r ^ 2))⁻¹ := by
  have hsq : ‖p r 2 - p r 4‖ ^ 2 = (Real.sqrt (4 - r ^ 2)) ^ 2 := by
    simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three,
      cos_four_pi_div_three, sin_four_pi_div_three, cos_five_pi_div_three,
      sin_five_pi_div_three, cos_pi_div_three, sin_pi_div_three]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
    try rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
    ring_nf
    try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_U hr hr1) hsq

lemma d25 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 2 - p r 5‖⁻¹ = (2 * Real.sqrt (1 - r ^ 2))⁻¹ := by
  have hsq : ‖p r 2 - p r 5‖ ^ 2 = (2 * Real.sqrt (1 - r ^ 2)) ^ 2 := by
    simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three,
      cos_four_pi_div_three, sin_four_pi_div_three, cos_five_pi_div_three,
      sin_five_pi_div_three, cos_pi_div_three, sin_pi_div_three]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
    try rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
    ring_nf
    try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_S hr hr1) hsq

lemma d26 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 2 - p r 6‖⁻¹ = (Real.sqrt (2 + 2 * r))⁻¹ := by
  have hsq : ‖p r 2 - p r 6‖ ^ 2 = (Real.sqrt (2 + 2 * r)) ^ 2 := by
    simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three,
      cos_four_pi_div_three, sin_four_pi_div_three, cos_five_pi_div_three,
      sin_five_pi_div_three, cos_pi_div_three, sin_pi_div_three]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
    try rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
    ring_nf
    try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_W hr hr1) hsq

lemma d27 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 2 - p r 7‖⁻¹ = (Real.sqrt (2 - r))⁻¹ := by
  have hsq : ‖p r 2 - p r 7‖ ^ 2 = (Real.sqrt (2 - r)) ^ 2 := by
    simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three,
      cos_four_pi_div_three, sin_four_pi_div_three, cos_five_pi_div_three,
      sin_five_pi_div_three, cos_pi_div_three, sin_pi_div_three]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
    try rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
    ring_nf
    try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_V hr hr1) hsq

lemma d28 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 2 - p r 8‖⁻¹ = (Real.sqrt (2 - r))⁻¹ := by
  have hsq : ‖p r 2 - p r 8‖ ^ 2 = (Real.sqrt (2 - r)) ^ 2 := by
    simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three,
      cos_four_pi_div_three, sin_four_pi_div_three, cos_five_pi_div_three,
      sin_five_pi_div_three, cos_pi_div_three, sin_pi_div_three]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
    try rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
    ring_nf
    try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_V hr hr1) hsq

lemma d34 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 3 - p r 4‖⁻¹ = (Real.sqrt 3 * r)⁻¹ := by
  have hsq : ‖p r 3 - p r 4‖ ^ 2 = (Real.sqrt 3 * r) ^ 2 := by
    simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three,
      cos_four_pi_div_three, sin_four_pi_div_three, cos_five_pi_div_three,
      sin_five_pi_div_three, cos_pi_div_three, sin_pi_div_three]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
    try rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
    ring_nf
    try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_T hr hr1) hsq

lemma d35 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 3 - p r 5‖⁻¹ = (Real.sqrt 3 * r)⁻¹ := by
  have hsq : ‖p r 3 - p r 5‖ ^ 2 = (Real.sqrt 3 * r) ^ 2 := by
    simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three,
      cos_four_pi_div_three, sin_four_pi_div_three, cos_five_pi_div_three,
      sin_five_pi_div_three, cos_pi_div_three, sin_pi_div_three]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
    try rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
    ring_nf
    try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_T hr hr1) hsq

lemma d36 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 3 - p r 6‖⁻¹ = (Real.sqrt (2 - r))⁻¹ := by
  have hsq : ‖p r 3 - p r 6‖ ^ 2 = (Real.sqrt (2 - r)) ^ 2 := by
    simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three,
      cos_four_pi_div_three, sin_four_pi_div_three, cos_five_pi_div_three,
      sin_five_pi_div_three, cos_pi_div_three, sin_pi_div_three]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
    try rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
    ring_nf
    try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_V hr hr1) hsq

lemma d37 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 3 - p r 7‖⁻¹ = (Real.sqrt (2 + 2 * r))⁻¹ := by
  have hsq : ‖p r 3 - p r 7‖ ^ 2 = (Real.sqrt (2 + 2 * r)) ^ 2 := by
    simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three,
      cos_four_pi_div_three, sin_four_pi_div_three, cos_five_pi_div_three,
      sin_five_pi_div_three, cos_pi_div_three, sin_pi_div_three]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
    try rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
    ring_nf
    try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_W hr hr1) hsq

lemma d38 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 3 - p r 8‖⁻¹ = (Real.sqrt (2 - r))⁻¹ := by
  have hsq : ‖p r 3 - p r 8‖ ^ 2 = (Real.sqrt (2 - r)) ^ 2 := by
    simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three,
      cos_four_pi_div_three, sin_four_pi_div_three, cos_five_pi_div_three,
      sin_five_pi_div_three, cos_pi_div_three, sin_pi_div_three]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
    try rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
    ring_nf
    try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_V hr hr1) hsq

lemma d45 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 4 - p r 5‖⁻¹ = (Real.sqrt 3 * r)⁻¹ := by
  have hsq : ‖p r 4 - p r 5‖ ^ 2 = (Real.sqrt 3 * r) ^ 2 := by
    simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three,
      cos_four_pi_div_three, sin_four_pi_div_three, cos_five_pi_div_three,
      sin_five_pi_div_three, cos_pi_div_three, sin_pi_div_three]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
    try rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
    ring_nf
    try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_T hr hr1) hsq

lemma d46 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 4 - p r 6‖⁻¹ = (Real.sqrt (2 - r))⁻¹ := by
  have hsq : ‖p r 4 - p r 6‖ ^ 2 = (Real.sqrt (2 - r)) ^ 2 := by
    simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three,
      cos_four_pi_div_three, sin_four_pi_div_three, cos_five_pi_div_three,
      sin_five_pi_div_three, cos_pi_div_three, sin_pi_div_three]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
    try rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
    ring_nf
    try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_V hr hr1) hsq

lemma d47 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 4 - p r 7‖⁻¹ = (Real.sqrt (2 - r))⁻¹ := by
  have hsq : ‖p r 4 - p r 7‖ ^ 2 = (Real.sqrt (2 - r)) ^ 2 := by
    simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three,
      cos_four_pi_div_three, sin_four_pi_div_three, cos_five_pi_div_three,
      sin_five_pi_div_three, cos_pi_div_three, sin_pi_div_three]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
    try rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
    ring_nf
    try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_V hr hr1) hsq

lemma d48 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 4 - p r 8‖⁻¹ = (Real.sqrt (2 + 2 * r))⁻¹ := by
  have hsq : ‖p r 4 - p r 8‖ ^ 2 = (Real.sqrt (2 + 2 * r)) ^ 2 := by
    simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three,
      cos_four_pi_div_three, sin_four_pi_div_three, cos_five_pi_div_three,
      sin_five_pi_div_three, cos_pi_div_three, sin_pi_div_three]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
    try rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
    ring_nf
    try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_W hr hr1) hsq

lemma d56 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 5 - p r 6‖⁻¹ = (Real.sqrt (2 + 2 * r))⁻¹ := by
  have hsq : ‖p r 5 - p r 6‖ ^ 2 = (Real.sqrt (2 + 2 * r)) ^ 2 := by
    simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three,
      cos_four_pi_div_three, sin_four_pi_div_three, cos_five_pi_div_three,
      sin_five_pi_div_three, cos_pi_div_three, sin_pi_div_three]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
    try rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
    ring_nf
    try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_W hr hr1) hsq

lemma d57 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 5 - p r 7‖⁻¹ = (Real.sqrt (2 - r))⁻¹ := by
  have hsq : ‖p r 5 - p r 7‖ ^ 2 = (Real.sqrt (2 - r)) ^ 2 := by
    simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three,
      cos_four_pi_div_three, sin_four_pi_div_three, cos_five_pi_div_three,
      sin_five_pi_div_three, cos_pi_div_three, sin_pi_div_three]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
    try rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
    ring_nf
    try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_V hr hr1) hsq

lemma d58 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 5 - p r 8‖⁻¹ = (Real.sqrt (2 - r))⁻¹ := by
  have hsq : ‖p r 5 - p r 8‖ ^ 2 = (Real.sqrt (2 - r)) ^ 2 := by
    simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three,
      cos_four_pi_div_three, sin_four_pi_div_three, cos_five_pi_div_three,
      sin_five_pi_div_three, cos_pi_div_three, sin_pi_div_three]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
    try rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
    ring_nf
    try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_V hr hr1) hsq

lemma d67 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 6 - p r 7‖⁻¹ = (Real.sqrt 3)⁻¹ := by
  have hsq : ‖p r 6 - p r 7‖ ^ 2 = (Real.sqrt 3) ^ 2 := by
    simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three,
      cos_four_pi_div_three, sin_four_pi_div_three, cos_five_pi_div_three,
      sin_five_pi_div_three, cos_pi_div_three, sin_pi_div_three]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
    try rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
    ring_nf
    try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_E3 hr hr1) hsq

lemma d68 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 6 - p r 8‖⁻¹ = (Real.sqrt 3)⁻¹ := by
  have hsq : ‖p r 6 - p r 8‖ ^ 2 = (Real.sqrt 3) ^ 2 := by
    simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three,
      cos_four_pi_div_three, sin_four_pi_div_three, cos_five_pi_div_three,
      sin_five_pi_div_three, cos_pi_div_three, sin_pi_div_three]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
    try rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
    ring_nf
    try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_E3 hr hr1) hsq

lemma d78 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 7 - p r 8‖⁻¹ = (Real.sqrt 3)⁻¹ := by
  have hsq : ‖p r 7 - p r 8‖ ^ 2 = (Real.sqrt 3) ^ 2 := by
    simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three,
      cos_four_pi_div_three, sin_four_pi_div_three, cos_five_pi_div_three,
      sin_five_pi_div_three, cos_pi_div_three, sin_pi_div_three]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
    try rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
    ring_nf
    try rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    try rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
    try ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_E3 hr hr1) hsq

lemma candidate_eq_p (r : ℝ) : candidate r = p r := by
  funext i
  fin_cases i <;> simp [candidate, p] <;> ring_nf

lemma familyEnergy_alt {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    familyEnergy r = 3 * (Real.sqrt 3)⁻¹ + 6 * (Real.sqrt 3 * r)⁻¹
      + 3 / (2 * Real.sqrt (1 - r ^ 2)) + 6 / Real.sqrt (4 - r ^ 2)
      + 12 / Real.sqrt (2 - r) + 6 / Real.sqrt (2 + 2 * r) := by
  unfold familyEnergy
  nth_rewrite 1 [sqrt3_eq_inv]
  rw [sqrt3_div_r hr]

lemma energy_p (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    energy (p r) = familyEnergy r := by
  unfold energy
  simp only [← Finset.filter_lt_eq_Ioi, Finset.sum_filter]
  simp [Fin.sum_univ_succ]
  rw [d01 r hr hr1, d02 r hr hr1, d03 r hr hr1, d04 r hr hr1, d05 r hr hr1,
    d06 r hr hr1, d07 r hr hr1, d08 r hr hr1, d12 r hr hr1, d13 r hr hr1,
    d14 r hr hr1, d15 r hr hr1, d16 r hr hr1, d17 r hr hr1, d18 r hr hr1,
    d23 r hr hr1, d24 r hr hr1, d25 r hr hr1, d26 r hr hr1, d27 r hr hr1,
    d28 r hr hr1, d34 r hr hr1, d35 r hr hr1, d36 r hr hr1, d37 r hr hr1,
    d38 r hr hr1, d45 r hr hr1, d46 r hr hr1, d47 r hr hr1, d48 r hr hr1,
    d56 r hr hr1, d57 r hr hr1, d58 r hr hr1, d67 r hr hr1, d68 r hr hr1,
    d78 r hr hr1]
  rw [familyEnergy_alt hr hr1]
  ring

lemma energy_candidate (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    energy (candidate r) = familyEnergy r := by
  rw [candidate_eq_p]
  exact energy_p r hr hr1

end Family
end ThomsonNine
