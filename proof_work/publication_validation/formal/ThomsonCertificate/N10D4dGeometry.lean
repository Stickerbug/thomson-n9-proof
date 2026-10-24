import ThomsonNine.Statement
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Geometry of the ten-point D4d family

The definition below is an exact coordinate model for the numerical D4d
candidate: two antipodal poles, two square rings at heights `-h` and `h`, and
the upper ring rotated by 45 degrees.  This file proves only the unit-sphere
property.  Injectivity, the energy identity, stationarity, and global
minimality are separate obligations.
-/

namespace ThomsonTen

open ThomsonNine

noncomputable def d4dRadius (h : ℝ) : ℝ := Real.sqrt (1 - h ^ 2)

noncomputable def d4dDiag (h : ℝ) : ℝ :=
  (Real.sqrt 2 / 2) * d4dRadius h

noncomputable def d4dConfig (h : ℝ) : Fin 10 → R3 :=
  ![
    !₂[0, 0, 1],
    !₂[0, 0, -1],
    !₂[d4dRadius h, 0, -h],
    !₂[0, d4dRadius h, -h],
    !₂[-d4dRadius h, 0, -h],
    !₂[0, -d4dRadius h, -h],
    !₂[d4dDiag h, d4dDiag h, h],
    !₂[-d4dDiag h, d4dDiag h, h],
    !₂[-d4dDiag h, -d4dDiag h, h],
    !₂[d4dDiag h, -d4dDiag h, h]
  ]

lemma norm_sq_vec (x y z : ℝ) :
    ‖(!₂[x, y, z] : R3)‖ ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_three]

lemma d4dRadius_sq {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    d4dRadius h ^ 2 = 1 - h ^ 2 := by
  rw [d4dRadius, Real.sq_sqrt]
  nlinarith

lemma d4dDiag_sq {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    d4dDiag h ^ 2 = (1 - h ^ 2) / 2 := by
  rw [d4dDiag, mul_pow, div_pow, Real.sq_sqrt]
  · rw [d4dRadius_sq hh0 hh1]
    norm_num
    ring
  · nlinarith

lemma d4d_norm_sq {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (i : Fin 10) :
    ‖d4dConfig h i‖ ^ 2 = 1 := by
  fin_cases i <;>
    simp [d4dConfig, norm_sq_vec, d4dRadius_sq hh0 hh1,
      d4dDiag_sq hh0 hh1]

theorem d4d_norm {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (i : Fin 10) :
    ‖d4dConfig h i‖ = 1 := by
  have hs := d4d_norm_sq hh0 hh1 i
  nlinarith [norm_nonneg (d4dConfig h i)]

theorem d4d_all_on_unit_sphere {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    ∀ i : Fin 10, ‖d4dConfig h i‖ = 1 :=
  fun i => d4d_norm hh0 hh1 i

lemma d4dRadius_pos {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    0 < d4dRadius h := by
  rw [d4dRadius, Real.sqrt_pos]
  nlinarith

lemma d4dDiag_pos {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    0 < d4dDiag h := by
  rw [d4dDiag]
  have hr : 0 < d4dRadius h := d4dRadius_pos hh0 hh1
  positivity

theorem d4d_injective {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    Function.Injective (d4dConfig h) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [d4dConfig] at hij ⊢
  all_goals
    have hr := d4dRadius_pos hh0 hh1
    have hd := d4dDiag_pos hh0 hh1
    try rcases hij with ⟨hij1, hij2⟩
    try rcases hij2 with ⟨hij2a, hij2b⟩
    nlinarith

theorem d4d_mem_sphereConfig {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    d4dConfig h ∈ SphereConfig 10 := by
  constructor
  · exact d4d_all_on_unit_sphere (le_of_lt hh0) (le_of_lt hh1)
  · exact d4d_injective hh0 hh1

lemma inv_eq_of_sq_eq_sq {h₀ d : ℝ} (hh : 0 ≤ h₀) (hd : 0 < d)
    (hsq : h₀ ^ 2 = d ^ 2) : h₀⁻¹ = d⁻¹ := by
  have heq : h₀ = d := by
    nlinarith [sq_nonneg (h₀ - d), sq_nonneg (h₀ + d)]
  rw [heq]

lemma norm_sq_sub_vec (x₁ y₁ z₁ x₂ y₂ z₂ : ℝ) :
    ‖(!₂[x₁, y₁, z₁] : R3) - !₂[x₂, y₂, z₂]‖ ^ 2 =
      (x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2 + (z₁ - z₂) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_three]

lemma pos_sqrt_two_add_two_mul {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    0 < Real.sqrt (2 + 2 * h) := by
  apply Real.sqrt_pos.mpr
  linarith

lemma pos_sqrt_two_sub_two_mul {h : ℝ} (_hh0 : 0 < h) (hh1 : h < 1) :
    0 < Real.sqrt (2 - 2 * h) := by
  apply Real.sqrt_pos.mpr
  linarith

lemma pos_sqrt_two_sub_two_sq {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    0 < Real.sqrt (2 - 2 * h ^ 2) := by
  apply Real.sqrt_pos.mpr
  nlinarith

lemma pos_two_radius {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    0 < 2 * d4dRadius h := by
  have hr := d4dRadius_pos hh0 hh1
  positivity

lemma sqrt_two_lt_two : Real.sqrt 2 < (2 : ℝ) := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]

lemma pos_sqrt_cross_minus {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    0 < Real.sqrt (2 + 2 * h ^ 2 - Real.sqrt 2 * (1 - h ^ 2)) := by
  apply Real.sqrt_pos.mpr
  have hs : Real.sqrt 2 < (2 : ℝ) := sqrt_two_lt_two
  have hp : 0 < h ^ 2 := sq_pos_of_pos hh0
  have ho : 0 < 1 - h ^ 2 := by nlinarith
  have hm := mul_lt_mul_of_pos_right hs ho
  nlinarith

lemma pos_sqrt_cross_plus {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    0 < Real.sqrt (2 + 2 * h ^ 2 + Real.sqrt 2 * (1 - h ^ 2)) := by
  apply Real.sqrt_pos.mpr
  have hp : 0 ≤ h ^ 2 := sq_nonneg h
  have ho : 0 ≤ 1 - h ^ 2 := by nlinarith
  have hm : 0 ≤ Real.sqrt 2 * (1 - h ^ 2) :=
    mul_nonneg (Real.sqrt_nonneg (2 : ℝ)) ho
  nlinarith

lemma d4d_pair_02 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 0 - d4dConfig h 2‖⁻¹ =
      (Real.sqrt (2 + 2 * h))⁻¹ := by
  have hsq : ‖d4dConfig h 0 - d4dConfig h 2‖ ^ 2 =
      (Real.sqrt (2 + 2 * h)) ^ 2 := by
    change ‖(!₂[0, 0, 1] : R3) - !₂[d4dRadius h, 0, -h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    ring_nf
    rw [d4dRadius_sq (le_of_lt hh0) (le_of_lt hh1)]
    rw [Real.sq_sqrt (by linarith)]
    ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_two_add_two_mul hh0 hh1) hsq

lemma d4d_pair_03 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 0 - d4dConfig h 3‖⁻¹ =
      (Real.sqrt (2 + 2 * h))⁻¹ := by
  have hsq : ‖d4dConfig h 0 - d4dConfig h 3‖ ^ 2 =
      (Real.sqrt (2 + 2 * h)) ^ 2 := by
    change ‖(!₂[0, 0, 1] : R3) - !₂[0, d4dRadius h, -h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    ring_nf
    rw [d4dRadius_sq (le_of_lt hh0) (le_of_lt hh1)]
    rw [Real.sq_sqrt (by linarith)]
    ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_two_add_two_mul hh0 hh1) hsq

lemma d4d_pair_04 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 0 - d4dConfig h 4‖⁻¹ =
      (Real.sqrt (2 + 2 * h))⁻¹ := by
  have hsq : ‖d4dConfig h 0 - d4dConfig h 4‖ ^ 2 =
      (Real.sqrt (2 + 2 * h)) ^ 2 := by
    change ‖(!₂[0, 0, 1] : R3) - !₂[-d4dRadius h, 0, -h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    ring_nf
    rw [d4dRadius_sq (le_of_lt hh0) (le_of_lt hh1)]
    rw [Real.sq_sqrt (by linarith)]
    ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_two_add_two_mul hh0 hh1) hsq

lemma d4d_pair_05 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 0 - d4dConfig h 5‖⁻¹ =
      (Real.sqrt (2 + 2 * h))⁻¹ := by
  have hsq : ‖d4dConfig h 0 - d4dConfig h 5‖ ^ 2 =
      (Real.sqrt (2 + 2 * h)) ^ 2 := by
    change ‖(!₂[0, 0, 1] : R3) - !₂[0, -d4dRadius h, -h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    ring_nf
    rw [d4dRadius_sq (le_of_lt hh0) (le_of_lt hh1)]
    rw [Real.sq_sqrt (by linarith)]
    ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_two_add_two_mul hh0 hh1) hsq

lemma d4d_pair_01 {h : ℝ} (_hh0 : 0 < h) (_hh1 : h < 1) :
    ‖d4dConfig h 0 - d4dConfig h 1‖⁻¹ = (2 : ℝ)⁻¹ := by
  have hsq : ‖d4dConfig h 0 - d4dConfig h 1‖ ^ 2 = (2 : ℝ) ^ 2 := by
    change ‖(!₂[0, 0, 1] : R3) - !₂[0, 0, -1]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    norm_num
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (by norm_num) hsq

lemma d4d_pair_06 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 0 - d4dConfig h 6‖⁻¹ =
      (Real.sqrt (2 - 2 * h))⁻¹ := by
  have hsq : ‖d4dConfig h 0 - d4dConfig h 6‖ ^ 2 =
      (Real.sqrt (2 - 2 * h)) ^ 2 := by
    change ‖(!₂[0, 0, 1] : R3) - !₂[d4dDiag h, d4dDiag h, h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    ring_nf
    rw [d4dDiag_sq (le_of_lt hh0) (le_of_lt hh1)]
    ring_nf
    rw [Real.sq_sqrt (by linarith)]
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_two_sub_two_mul hh0 hh1) hsq

lemma d4d_pair_07 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 0 - d4dConfig h 7‖⁻¹ =
      (Real.sqrt (2 - 2 * h))⁻¹ := by
  have hsq : ‖d4dConfig h 0 - d4dConfig h 7‖ ^ 2 =
      (Real.sqrt (2 - 2 * h)) ^ 2 := by
    change ‖(!₂[0, 0, 1] : R3) - !₂[-d4dDiag h, d4dDiag h, h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    ring_nf
    rw [d4dDiag_sq (le_of_lt hh0) (le_of_lt hh1)]
    ring_nf
    rw [Real.sq_sqrt (by linarith)]
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_two_sub_two_mul hh0 hh1) hsq

lemma d4d_pair_08 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 0 - d4dConfig h 8‖⁻¹ =
      (Real.sqrt (2 - 2 * h))⁻¹ := by
  have hsq : ‖d4dConfig h 0 - d4dConfig h 8‖ ^ 2 =
      (Real.sqrt (2 - 2 * h)) ^ 2 := by
    change ‖(!₂[0, 0, 1] : R3) - !₂[-d4dDiag h, -d4dDiag h, h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    ring_nf
    rw [d4dDiag_sq (le_of_lt hh0) (le_of_lt hh1)]
    ring_nf
    rw [Real.sq_sqrt (by linarith)]
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_two_sub_two_mul hh0 hh1) hsq

lemma d4d_pair_09 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 0 - d4dConfig h 9‖⁻¹ =
      (Real.sqrt (2 - 2 * h))⁻¹ := by
  have hsq : ‖d4dConfig h 0 - d4dConfig h 9‖ ^ 2 =
      (Real.sqrt (2 - 2 * h)) ^ 2 := by
    change ‖(!₂[0, 0, 1] : R3) - !₂[d4dDiag h, -d4dDiag h, h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    ring_nf
    rw [d4dDiag_sq (le_of_lt hh0) (le_of_lt hh1)]
    ring_nf
    rw [Real.sq_sqrt (by linarith)]
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_two_sub_two_mul hh0 hh1) hsq

lemma d4d_pair_12 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 1 - d4dConfig h 2‖⁻¹ =
      (Real.sqrt (2 - 2 * h))⁻¹ := by
  have hsq : ‖d4dConfig h 1 - d4dConfig h 2‖ ^ 2 =
      (Real.sqrt (2 - 2 * h)) ^ 2 := by
    change ‖(!₂[0, 0, -1] : R3) - !₂[d4dRadius h, 0, -h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    ring_nf
    rw [d4dRadius_sq (le_of_lt hh0) (le_of_lt hh1)]
    rw [Real.sq_sqrt (by linarith)]
    ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_two_sub_two_mul hh0 hh1) hsq

lemma d4d_pair_13 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 1 - d4dConfig h 3‖⁻¹ =
      (Real.sqrt (2 - 2 * h))⁻¹ := by
  have hsq : ‖d4dConfig h 1 - d4dConfig h 3‖ ^ 2 =
      (Real.sqrt (2 - 2 * h)) ^ 2 := by
    change ‖(!₂[0, 0, -1] : R3) - !₂[0, d4dRadius h, -h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    ring_nf
    rw [d4dRadius_sq (le_of_lt hh0) (le_of_lt hh1)]
    rw [Real.sq_sqrt (by linarith)]
    ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_two_sub_two_mul hh0 hh1) hsq

lemma d4d_pair_14 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 1 - d4dConfig h 4‖⁻¹ =
      (Real.sqrt (2 - 2 * h))⁻¹ := by
  have hsq : ‖d4dConfig h 1 - d4dConfig h 4‖ ^ 2 =
      (Real.sqrt (2 - 2 * h)) ^ 2 := by
    change ‖(!₂[0, 0, -1] : R3) - !₂[-d4dRadius h, 0, -h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    ring_nf
    rw [d4dRadius_sq (le_of_lt hh0) (le_of_lt hh1)]
    rw [Real.sq_sqrt (by linarith)]
    ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_two_sub_two_mul hh0 hh1) hsq

lemma d4d_pair_15 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 1 - d4dConfig h 5‖⁻¹ =
      (Real.sqrt (2 - 2 * h))⁻¹ := by
  have hsq : ‖d4dConfig h 1 - d4dConfig h 5‖ ^ 2 =
      (Real.sqrt (2 - 2 * h)) ^ 2 := by
    change ‖(!₂[0, 0, -1] : R3) - !₂[0, -d4dRadius h, -h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    ring_nf
    rw [d4dRadius_sq (le_of_lt hh0) (le_of_lt hh1)]
    rw [Real.sq_sqrt (by linarith)]
    ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_two_sub_two_mul hh0 hh1) hsq

lemma d4d_pair_16 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 1 - d4dConfig h 6‖⁻¹ =
      (Real.sqrt (2 + 2 * h))⁻¹ := by
  have hsq : ‖d4dConfig h 1 - d4dConfig h 6‖ ^ 2 =
      (Real.sqrt (2 + 2 * h)) ^ 2 := by
    change ‖(!₂[0, 0, -1] : R3) - !₂[d4dDiag h, d4dDiag h, h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    ring_nf
    rw [d4dDiag_sq (le_of_lt hh0) (le_of_lt hh1)]
    ring_nf
    rw [Real.sq_sqrt (by linarith)]
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_two_add_two_mul hh0 hh1) hsq

lemma d4d_pair_17 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 1 - d4dConfig h 7‖⁻¹ =
      (Real.sqrt (2 + 2 * h))⁻¹ := by
  have hsq : ‖d4dConfig h 1 - d4dConfig h 7‖ ^ 2 =
      (Real.sqrt (2 + 2 * h)) ^ 2 := by
    change ‖(!₂[0, 0, -1] : R3) - !₂[-d4dDiag h, d4dDiag h, h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    ring_nf
    rw [d4dDiag_sq (le_of_lt hh0) (le_of_lt hh1)]
    ring_nf
    rw [Real.sq_sqrt (by linarith)]
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_two_add_two_mul hh0 hh1) hsq

lemma d4d_pair_18 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 1 - d4dConfig h 8‖⁻¹ =
      (Real.sqrt (2 + 2 * h))⁻¹ := by
  have hsq : ‖d4dConfig h 1 - d4dConfig h 8‖ ^ 2 =
      (Real.sqrt (2 + 2 * h)) ^ 2 := by
    change ‖(!₂[0, 0, -1] : R3) - !₂[-d4dDiag h, -d4dDiag h, h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    ring_nf
    rw [d4dDiag_sq (le_of_lt hh0) (le_of_lt hh1)]
    ring_nf
    rw [Real.sq_sqrt (by linarith)]
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_two_add_two_mul hh0 hh1) hsq

lemma d4d_pair_19 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 1 - d4dConfig h 9‖⁻¹ =
      (Real.sqrt (2 + 2 * h))⁻¹ := by
  have hsq : ‖d4dConfig h 1 - d4dConfig h 9‖ ^ 2 =
      (Real.sqrt (2 + 2 * h)) ^ 2 := by
    change ‖(!₂[0, 0, -1] : R3) - !₂[d4dDiag h, -d4dDiag h, h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    ring_nf
    rw [d4dDiag_sq (le_of_lt hh0) (le_of_lt hh1)]
    ring_nf
    rw [Real.sq_sqrt (by linarith)]
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_two_add_two_mul hh0 hh1) hsq

lemma d4d_pair_23 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 2 - d4dConfig h 3‖⁻¹ =
      (Real.sqrt (2 - 2 * h ^ 2))⁻¹ := by
  have hsq : ‖d4dConfig h 2 - d4dConfig h 3‖ ^ 2 =
      (Real.sqrt (2 - 2 * h ^ 2)) ^ 2 := by
    change ‖(!₂[d4dRadius h, 0, -h] : R3) - !₂[0, d4dRadius h, -h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    ring_nf
    rw [d4dRadius_sq (le_of_lt hh0) (le_of_lt hh1)]
    rw [Real.sq_sqrt (by nlinarith)]
    ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_two_sub_two_sq hh0 hh1) hsq

lemma d4d_pair_24 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 2 - d4dConfig h 4‖⁻¹ =
      (2 * d4dRadius h)⁻¹ := by
  have hsq : ‖d4dConfig h 2 - d4dConfig h 4‖ ^ 2 =
      (2 * d4dRadius h) ^ 2 := by
    change ‖(!₂[d4dRadius h, 0, -h] : R3) - !₂[-d4dRadius h, 0, -h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    ring_nf
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_two_radius hh0 hh1) hsq

lemma d4d_pair_25 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 2 - d4dConfig h 5‖⁻¹ =
      (Real.sqrt (2 - 2 * h ^ 2))⁻¹ := by
  have hsq : ‖d4dConfig h 2 - d4dConfig h 5‖ ^ 2 =
      (Real.sqrt (2 - 2 * h ^ 2)) ^ 2 := by
    change ‖(!₂[d4dRadius h, 0, -h] : R3) - !₂[0, -d4dRadius h, -h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    ring_nf
    rw [d4dRadius_sq (le_of_lt hh0) (le_of_lt hh1)]
    rw [Real.sq_sqrt (by nlinarith)]
    ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_two_sub_two_sq hh0 hh1) hsq

lemma d4d_pair_34 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 3 - d4dConfig h 4‖⁻¹ =
      (Real.sqrt (2 - 2 * h ^ 2))⁻¹ := by
  have hsq : ‖d4dConfig h 3 - d4dConfig h 4‖ ^ 2 =
      (Real.sqrt (2 - 2 * h ^ 2)) ^ 2 := by
    change ‖(!₂[0, d4dRadius h, -h] : R3) - !₂[-d4dRadius h, 0, -h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    ring_nf
    rw [d4dRadius_sq (le_of_lt hh0) (le_of_lt hh1)]
    rw [Real.sq_sqrt (by nlinarith)]
    ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_two_sub_two_sq hh0 hh1) hsq

lemma d4d_pair_35 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 3 - d4dConfig h 5‖⁻¹ =
      (2 * d4dRadius h)⁻¹ := by
  have hsq : ‖d4dConfig h 3 - d4dConfig h 5‖ ^ 2 =
      (2 * d4dRadius h) ^ 2 := by
    change ‖(!₂[0, d4dRadius h, -h] : R3) - !₂[0, -d4dRadius h, -h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    ring_nf
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_two_radius hh0 hh1) hsq

lemma d4d_pair_45 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 4 - d4dConfig h 5‖⁻¹ =
      (Real.sqrt (2 - 2 * h ^ 2))⁻¹ := by
  have hsq : ‖d4dConfig h 4 - d4dConfig h 5‖ ^ 2 =
      (Real.sqrt (2 - 2 * h ^ 2)) ^ 2 := by
    change ‖(!₂[-d4dRadius h, 0, -h] : R3) - !₂[0, -d4dRadius h, -h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    ring_nf
    rw [d4dRadius_sq (le_of_lt hh0) (le_of_lt hh1)]
    rw [Real.sq_sqrt (by nlinarith)]
    ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_two_sub_two_sq hh0 hh1) hsq

lemma d4d_pair_67 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 6 - d4dConfig h 7‖⁻¹ =
      (Real.sqrt (2 - 2 * h ^ 2))⁻¹ := by
  have hsq : ‖d4dConfig h 6 - d4dConfig h 7‖ ^ 2 =
      (Real.sqrt (2 - 2 * h ^ 2)) ^ 2 := by
    change ‖(!₂[d4dDiag h, d4dDiag h, h] : R3) - !₂[-d4dDiag h, d4dDiag h, h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    ring_nf
    rw [d4dDiag_sq (le_of_lt hh0) (le_of_lt hh1)]
    rw [Real.sq_sqrt (by nlinarith)]
    ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_two_sub_two_sq hh0 hh1) hsq

lemma d4d_pair_68 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 6 - d4dConfig h 8‖⁻¹ =
      (2 * d4dRadius h)⁻¹ := by
  have hsq : ‖d4dConfig h 6 - d4dConfig h 8‖ ^ 2 =
      (2 * d4dRadius h) ^ 2 := by
    change ‖(!₂[d4dDiag h, d4dDiag h, h] : R3) - !₂[-d4dDiag h, -d4dDiag h, h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    ring_nf
    rw [d4dDiag_sq (le_of_lt hh0) (le_of_lt hh1)]
    rw [d4dRadius_sq (le_of_lt hh0) (le_of_lt hh1)]
    ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_two_radius hh0 hh1) hsq

lemma d4d_pair_69 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 6 - d4dConfig h 9‖⁻¹ =
      (Real.sqrt (2 - 2 * h ^ 2))⁻¹ := by
  have hsq : ‖d4dConfig h 6 - d4dConfig h 9‖ ^ 2 =
      (Real.sqrt (2 - 2 * h ^ 2)) ^ 2 := by
    change ‖(!₂[d4dDiag h, d4dDiag h, h] : R3) - !₂[d4dDiag h, -d4dDiag h, h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    ring_nf
    rw [d4dDiag_sq (le_of_lt hh0) (le_of_lt hh1)]
    rw [Real.sq_sqrt (by nlinarith)]
    ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_two_sub_two_sq hh0 hh1) hsq

lemma d4d_pair_78 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 7 - d4dConfig h 8‖⁻¹ =
      (Real.sqrt (2 - 2 * h ^ 2))⁻¹ := by
  have hsq : ‖d4dConfig h 7 - d4dConfig h 8‖ ^ 2 =
      (Real.sqrt (2 - 2 * h ^ 2)) ^ 2 := by
    change ‖(!₂[-d4dDiag h, d4dDiag h, h] : R3) - !₂[-d4dDiag h, -d4dDiag h, h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    ring_nf
    rw [d4dDiag_sq (le_of_lt hh0) (le_of_lt hh1)]
    rw [Real.sq_sqrt (by nlinarith)]
    ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_two_sub_two_sq hh0 hh1) hsq

lemma d4d_pair_79 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 7 - d4dConfig h 9‖⁻¹ =
      (2 * d4dRadius h)⁻¹ := by
  have hsq : ‖d4dConfig h 7 - d4dConfig h 9‖ ^ 2 =
      (2 * d4dRadius h) ^ 2 := by
    change ‖(!₂[-d4dDiag h, d4dDiag h, h] : R3) - !₂[d4dDiag h, -d4dDiag h, h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    ring_nf
    rw [d4dDiag_sq (le_of_lt hh0) (le_of_lt hh1)]
    rw [d4dRadius_sq (le_of_lt hh0) (le_of_lt hh1)]
    ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_two_radius hh0 hh1) hsq

lemma d4d_pair_89 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 8 - d4dConfig h 9‖⁻¹ =
      (Real.sqrt (2 - 2 * h ^ 2))⁻¹ := by
  have hsq : ‖d4dConfig h 8 - d4dConfig h 9‖ ^ 2 =
      (Real.sqrt (2 - 2 * h ^ 2)) ^ 2 := by
    change ‖(!₂[-d4dDiag h, -d4dDiag h, h] : R3) - !₂[d4dDiag h, -d4dDiag h, h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    ring_nf
    rw [d4dDiag_sq (le_of_lt hh0) (le_of_lt hh1)]
    rw [Real.sq_sqrt (by nlinarith)]
    ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_two_sub_two_sq hh0 hh1) hsq

lemma d4d_pair_26 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 2 - d4dConfig h 6‖⁻¹ =
      (Real.sqrt (2 + 2 * h ^ 2 - Real.sqrt 2 * (1 - h ^ 2)))⁻¹ := by
  have hsq : ‖d4dConfig h 2 - d4dConfig h 6‖ ^ 2 =
      (Real.sqrt (2 + 2 * h ^ 2 - Real.sqrt 2 * (1 - h ^ 2))) ^ 2 := by
    change ‖(!₂[d4dRadius h, 0, -h] : R3) - !₂[d4dDiag h, d4dDiag h, h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    simp only [d4dDiag]
    have hc : 0 < 2 + 2 * h ^ 2 - Real.sqrt 2 * (1 - h ^ 2) :=
      Real.sqrt_pos.mp (pos_sqrt_cross_minus hh0 hh1)
    rw [Real.sq_sqrt (le_of_lt hc)]
    ring_nf
    rw [d4dRadius_sq (le_of_lt hh0) (le_of_lt hh1)]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_cross_minus hh0 hh1) hsq
lemma d4d_pair_27 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 2 - d4dConfig h 7‖⁻¹ = (Real.sqrt (2 + 2 * h ^ 2 + Real.sqrt 2 * (1 - h ^ 2)))⁻¹ := by
  have hsq : ‖d4dConfig h 2 - d4dConfig h 7‖ ^ 2 =
      (Real.sqrt (2 + 2 * h ^ 2 + Real.sqrt 2 * (1 - h ^ 2))) ^ 2 := by
    change ‖(!₂[d4dRadius h, 0, -h] : R3) - !₂[-d4dDiag h, d4dDiag h, h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    simp only [d4dDiag]
    have hc : 0 < 2 + 2 * h ^ 2 + Real.sqrt 2 * (1 - h ^ 2) :=
      Real.sqrt_pos.mp (pos_sqrt_cross_plus hh0 hh1)
    rw [Real.sq_sqrt (le_of_lt hc)]
    ring_nf
    rw [d4dRadius_sq (le_of_lt hh0) (le_of_lt hh1)]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_cross_plus hh0 hh1) hsq


lemma d4d_pair_28 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 2 - d4dConfig h 8‖⁻¹ = (Real.sqrt (2 + 2 * h ^ 2 + Real.sqrt 2 * (1 - h ^ 2)))⁻¹ := by
  have hsq : ‖d4dConfig h 2 - d4dConfig h 8‖ ^ 2 =
      (Real.sqrt (2 + 2 * h ^ 2 + Real.sqrt 2 * (1 - h ^ 2))) ^ 2 := by
    change ‖(!₂[d4dRadius h, 0, -h] : R3) - !₂[-d4dDiag h, -d4dDiag h, h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    simp only [d4dDiag]
    have hc : 0 < 2 + 2 * h ^ 2 + Real.sqrt 2 * (1 - h ^ 2) :=
      Real.sqrt_pos.mp (pos_sqrt_cross_plus hh0 hh1)
    rw [Real.sq_sqrt (le_of_lt hc)]
    ring_nf
    rw [d4dRadius_sq (le_of_lt hh0) (le_of_lt hh1)]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_cross_plus hh0 hh1) hsq


lemma d4d_pair_29 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 2 - d4dConfig h 9‖⁻¹ = (Real.sqrt (2 + 2 * h ^ 2 - Real.sqrt 2 * (1 - h ^ 2)))⁻¹ := by
  have hsq : ‖d4dConfig h 2 - d4dConfig h 9‖ ^ 2 =
      (Real.sqrt (2 + 2 * h ^ 2 - Real.sqrt 2 * (1 - h ^ 2))) ^ 2 := by
    change ‖(!₂[d4dRadius h, 0, -h] : R3) - !₂[d4dDiag h, -d4dDiag h, h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    simp only [d4dDiag]
    have hc : 0 < 2 + 2 * h ^ 2 - Real.sqrt 2 * (1 - h ^ 2) :=
      Real.sqrt_pos.mp (pos_sqrt_cross_minus hh0 hh1)
    rw [Real.sq_sqrt (le_of_lt hc)]
    ring_nf
    rw [d4dRadius_sq (le_of_lt hh0) (le_of_lt hh1)]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_cross_minus hh0 hh1) hsq


lemma d4d_pair_36 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 3 - d4dConfig h 6‖⁻¹ = (Real.sqrt (2 + 2 * h ^ 2 - Real.sqrt 2 * (1 - h ^ 2)))⁻¹ := by
  have hsq : ‖d4dConfig h 3 - d4dConfig h 6‖ ^ 2 =
      (Real.sqrt (2 + 2 * h ^ 2 - Real.sqrt 2 * (1 - h ^ 2))) ^ 2 := by
    change ‖(!₂[0, d4dRadius h, -h] : R3) - !₂[d4dDiag h, d4dDiag h, h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    simp only [d4dDiag]
    have hc : 0 < 2 + 2 * h ^ 2 - Real.sqrt 2 * (1 - h ^ 2) :=
      Real.sqrt_pos.mp (pos_sqrt_cross_minus hh0 hh1)
    rw [Real.sq_sqrt (le_of_lt hc)]
    ring_nf
    rw [d4dRadius_sq (le_of_lt hh0) (le_of_lt hh1)]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_cross_minus hh0 hh1) hsq


lemma d4d_pair_37 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 3 - d4dConfig h 7‖⁻¹ = (Real.sqrt (2 + 2 * h ^ 2 - Real.sqrt 2 * (1 - h ^ 2)))⁻¹ := by
  have hsq : ‖d4dConfig h 3 - d4dConfig h 7‖ ^ 2 =
      (Real.sqrt (2 + 2 * h ^ 2 - Real.sqrt 2 * (1 - h ^ 2))) ^ 2 := by
    change ‖(!₂[0, d4dRadius h, -h] : R3) - !₂[-d4dDiag h, d4dDiag h, h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    simp only [d4dDiag]
    have hc : 0 < 2 + 2 * h ^ 2 - Real.sqrt 2 * (1 - h ^ 2) :=
      Real.sqrt_pos.mp (pos_sqrt_cross_minus hh0 hh1)
    rw [Real.sq_sqrt (le_of_lt hc)]
    ring_nf
    rw [d4dRadius_sq (le_of_lt hh0) (le_of_lt hh1)]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_cross_minus hh0 hh1) hsq


lemma d4d_pair_38 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 3 - d4dConfig h 8‖⁻¹ = (Real.sqrt (2 + 2 * h ^ 2 + Real.sqrt 2 * (1 - h ^ 2)))⁻¹ := by
  have hsq : ‖d4dConfig h 3 - d4dConfig h 8‖ ^ 2 =
      (Real.sqrt (2 + 2 * h ^ 2 + Real.sqrt 2 * (1 - h ^ 2))) ^ 2 := by
    change ‖(!₂[0, d4dRadius h, -h] : R3) - !₂[-d4dDiag h, -d4dDiag h, h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    simp only [d4dDiag]
    have hc : 0 < 2 + 2 * h ^ 2 + Real.sqrt 2 * (1 - h ^ 2) :=
      Real.sqrt_pos.mp (pos_sqrt_cross_plus hh0 hh1)
    rw [Real.sq_sqrt (le_of_lt hc)]
    ring_nf
    rw [d4dRadius_sq (le_of_lt hh0) (le_of_lt hh1)]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_cross_plus hh0 hh1) hsq


lemma d4d_pair_39 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 3 - d4dConfig h 9‖⁻¹ = (Real.sqrt (2 + 2 * h ^ 2 + Real.sqrt 2 * (1 - h ^ 2)))⁻¹ := by
  have hsq : ‖d4dConfig h 3 - d4dConfig h 9‖ ^ 2 =
      (Real.sqrt (2 + 2 * h ^ 2 + Real.sqrt 2 * (1 - h ^ 2))) ^ 2 := by
    change ‖(!₂[0, d4dRadius h, -h] : R3) - !₂[d4dDiag h, -d4dDiag h, h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    simp only [d4dDiag]
    have hc : 0 < 2 + 2 * h ^ 2 + Real.sqrt 2 * (1 - h ^ 2) :=
      Real.sqrt_pos.mp (pos_sqrt_cross_plus hh0 hh1)
    rw [Real.sq_sqrt (le_of_lt hc)]
    ring_nf
    rw [d4dRadius_sq (le_of_lt hh0) (le_of_lt hh1)]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_cross_plus hh0 hh1) hsq


lemma d4d_pair_46 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 4 - d4dConfig h 6‖⁻¹ = (Real.sqrt (2 + 2 * h ^ 2 + Real.sqrt 2 * (1 - h ^ 2)))⁻¹ := by
  have hsq : ‖d4dConfig h 4 - d4dConfig h 6‖ ^ 2 =
      (Real.sqrt (2 + 2 * h ^ 2 + Real.sqrt 2 * (1 - h ^ 2))) ^ 2 := by
    change ‖(!₂[-d4dRadius h, 0, -h] : R3) - !₂[d4dDiag h, d4dDiag h, h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    simp only [d4dDiag]
    have hc : 0 < 2 + 2 * h ^ 2 + Real.sqrt 2 * (1 - h ^ 2) :=
      Real.sqrt_pos.mp (pos_sqrt_cross_plus hh0 hh1)
    rw [Real.sq_sqrt (le_of_lt hc)]
    ring_nf
    rw [d4dRadius_sq (le_of_lt hh0) (le_of_lt hh1)]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_cross_plus hh0 hh1) hsq


lemma d4d_pair_47 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 4 - d4dConfig h 7‖⁻¹ = (Real.sqrt (2 + 2 * h ^ 2 - Real.sqrt 2 * (1 - h ^ 2)))⁻¹ := by
  have hsq : ‖d4dConfig h 4 - d4dConfig h 7‖ ^ 2 =
      (Real.sqrt (2 + 2 * h ^ 2 - Real.sqrt 2 * (1 - h ^ 2))) ^ 2 := by
    change ‖(!₂[-d4dRadius h, 0, -h] : R3) - !₂[-d4dDiag h, d4dDiag h, h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    simp only [d4dDiag]
    have hc : 0 < 2 + 2 * h ^ 2 - Real.sqrt 2 * (1 - h ^ 2) :=
      Real.sqrt_pos.mp (pos_sqrt_cross_minus hh0 hh1)
    rw [Real.sq_sqrt (le_of_lt hc)]
    ring_nf
    rw [d4dRadius_sq (le_of_lt hh0) (le_of_lt hh1)]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_cross_minus hh0 hh1) hsq


lemma d4d_pair_48 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 4 - d4dConfig h 8‖⁻¹ = (Real.sqrt (2 + 2 * h ^ 2 - Real.sqrt 2 * (1 - h ^ 2)))⁻¹ := by
  have hsq : ‖d4dConfig h 4 - d4dConfig h 8‖ ^ 2 =
      (Real.sqrt (2 + 2 * h ^ 2 - Real.sqrt 2 * (1 - h ^ 2))) ^ 2 := by
    change ‖(!₂[-d4dRadius h, 0, -h] : R3) - !₂[-d4dDiag h, -d4dDiag h, h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    simp only [d4dDiag]
    have hc : 0 < 2 + 2 * h ^ 2 - Real.sqrt 2 * (1 - h ^ 2) :=
      Real.sqrt_pos.mp (pos_sqrt_cross_minus hh0 hh1)
    rw [Real.sq_sqrt (le_of_lt hc)]
    ring_nf
    rw [d4dRadius_sq (le_of_lt hh0) (le_of_lt hh1)]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_cross_minus hh0 hh1) hsq


lemma d4d_pair_49 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 4 - d4dConfig h 9‖⁻¹ = (Real.sqrt (2 + 2 * h ^ 2 + Real.sqrt 2 * (1 - h ^ 2)))⁻¹ := by
  have hsq : ‖d4dConfig h 4 - d4dConfig h 9‖ ^ 2 =
      (Real.sqrt (2 + 2 * h ^ 2 + Real.sqrt 2 * (1 - h ^ 2))) ^ 2 := by
    change ‖(!₂[-d4dRadius h, 0, -h] : R3) - !₂[d4dDiag h, -d4dDiag h, h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    simp only [d4dDiag]
    have hc : 0 < 2 + 2 * h ^ 2 + Real.sqrt 2 * (1 - h ^ 2) :=
      Real.sqrt_pos.mp (pos_sqrt_cross_plus hh0 hh1)
    rw [Real.sq_sqrt (le_of_lt hc)]
    ring_nf
    rw [d4dRadius_sq (le_of_lt hh0) (le_of_lt hh1)]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_cross_plus hh0 hh1) hsq


lemma d4d_pair_56 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 5 - d4dConfig h 6‖⁻¹ = (Real.sqrt (2 + 2 * h ^ 2 + Real.sqrt 2 * (1 - h ^ 2)))⁻¹ := by
  have hsq : ‖d4dConfig h 5 - d4dConfig h 6‖ ^ 2 =
      (Real.sqrt (2 + 2 * h ^ 2 + Real.sqrt 2 * (1 - h ^ 2))) ^ 2 := by
    change ‖(!₂[0, -d4dRadius h, -h] : R3) - !₂[d4dDiag h, d4dDiag h, h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    simp only [d4dDiag]
    have hc : 0 < 2 + 2 * h ^ 2 + Real.sqrt 2 * (1 - h ^ 2) :=
      Real.sqrt_pos.mp (pos_sqrt_cross_plus hh0 hh1)
    rw [Real.sq_sqrt (le_of_lt hc)]
    ring_nf
    rw [d4dRadius_sq (le_of_lt hh0) (le_of_lt hh1)]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_cross_plus hh0 hh1) hsq


lemma d4d_pair_57 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 5 - d4dConfig h 7‖⁻¹ = (Real.sqrt (2 + 2 * h ^ 2 + Real.sqrt 2 * (1 - h ^ 2)))⁻¹ := by
  have hsq : ‖d4dConfig h 5 - d4dConfig h 7‖ ^ 2 =
      (Real.sqrt (2 + 2 * h ^ 2 + Real.sqrt 2 * (1 - h ^ 2))) ^ 2 := by
    change ‖(!₂[0, -d4dRadius h, -h] : R3) - !₂[-d4dDiag h, d4dDiag h, h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    simp only [d4dDiag]
    have hc : 0 < 2 + 2 * h ^ 2 + Real.sqrt 2 * (1 - h ^ 2) :=
      Real.sqrt_pos.mp (pos_sqrt_cross_plus hh0 hh1)
    rw [Real.sq_sqrt (le_of_lt hc)]
    ring_nf
    rw [d4dRadius_sq (le_of_lt hh0) (le_of_lt hh1)]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_cross_plus hh0 hh1) hsq


lemma d4d_pair_58 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 5 - d4dConfig h 8‖⁻¹ = (Real.sqrt (2 + 2 * h ^ 2 - Real.sqrt 2 * (1 - h ^ 2)))⁻¹ := by
  have hsq : ‖d4dConfig h 5 - d4dConfig h 8‖ ^ 2 =
      (Real.sqrt (2 + 2 * h ^ 2 - Real.sqrt 2 * (1 - h ^ 2))) ^ 2 := by
    change ‖(!₂[0, -d4dRadius h, -h] : R3) - !₂[-d4dDiag h, -d4dDiag h, h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    simp only [d4dDiag]
    have hc : 0 < 2 + 2 * h ^ 2 - Real.sqrt 2 * (1 - h ^ 2) :=
      Real.sqrt_pos.mp (pos_sqrt_cross_minus hh0 hh1)
    rw [Real.sq_sqrt (le_of_lt hc)]
    ring_nf
    rw [d4dRadius_sq (le_of_lt hh0) (le_of_lt hh1)]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_cross_minus hh0 hh1) hsq


lemma d4d_pair_59 {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ‖d4dConfig h 5 - d4dConfig h 9‖⁻¹ = (Real.sqrt (2 + 2 * h ^ 2 - Real.sqrt 2 * (1 - h ^ 2)))⁻¹ := by
  have hsq : ‖d4dConfig h 5 - d4dConfig h 9‖ ^ 2 =
      (Real.sqrt (2 + 2 * h ^ 2 - Real.sqrt 2 * (1 - h ^ 2))) ^ 2 := by
    change ‖(!₂[0, -d4dRadius h, -h] : R3) - !₂[d4dDiag h, -d4dDiag h, h]‖ ^ 2 = _
    rw [norm_sq_sub_vec]
    simp only [d4dDiag]
    have hc : 0 < 2 + 2 * h ^ 2 - Real.sqrt 2 * (1 - h ^ 2) :=
      Real.sqrt_pos.mp (pos_sqrt_cross_minus hh0 hh1)
    rw [Real.sq_sqrt (le_of_lt hc)]
    ring_nf
    rw [d4dRadius_sq (le_of_lt hh0) (le_of_lt hh1)]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  exact inv_eq_of_sq_eq_sq (norm_nonneg _) (pos_sqrt_cross_minus hh0 hh1) hsq


noncomputable def d4dEnergyFormula (h : ℝ) : ℝ :=
    (2 : ℝ)⁻¹
      + 8 * (Real.sqrt (2 + 2 * h))⁻¹
      + 8 * (Real.sqrt (2 - 2 * h))⁻¹
      + 8 * (Real.sqrt (2 - 2 * h ^ 2))⁻¹
      + 4 * (2 * d4dRadius h)⁻¹
      + 8 * (Real.sqrt (2 + 2 * h ^ 2 -
          Real.sqrt 2 * (1 - h ^ 2)))⁻¹
      + 8 * (Real.sqrt (2 + 2 * h ^ 2 +
          Real.sqrt 2 * (1 - h ^ 2)))⁻¹

theorem d4d_energy_eq_formula {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    ThomsonNine.energy (d4dConfig h) = d4dEnergyFormula h := by
  unfold ThomsonNine.energy
  simp only [← Finset.filter_lt_eq_Ioi, Finset.sum_filter]
  simp [Fin.sum_univ_succ]
  rw [
    d4d_pair_01 (h := h) hh0 hh1,
    d4d_pair_02 (h := h) hh0 hh1,
    d4d_pair_03 (h := h) hh0 hh1,
    d4d_pair_04 (h := h) hh0 hh1,
    d4d_pair_05 (h := h) hh0 hh1,
    d4d_pair_06 (h := h) hh0 hh1,
    d4d_pair_07 (h := h) hh0 hh1,
    d4d_pair_08 (h := h) hh0 hh1,
    d4d_pair_09 (h := h) hh0 hh1,
    d4d_pair_12 (h := h) hh0 hh1,
    d4d_pair_13 (h := h) hh0 hh1,
    d4d_pair_14 (h := h) hh0 hh1,
    d4d_pair_15 (h := h) hh0 hh1,
    d4d_pair_16 (h := h) hh0 hh1,
    d4d_pair_17 (h := h) hh0 hh1,
    d4d_pair_18 (h := h) hh0 hh1,
    d4d_pair_19 (h := h) hh0 hh1,
    d4d_pair_23 (h := h) hh0 hh1,
    d4d_pair_24 (h := h) hh0 hh1,
    d4d_pair_25 (h := h) hh0 hh1,
    d4d_pair_34 (h := h) hh0 hh1,
    d4d_pair_35 (h := h) hh0 hh1,
    d4d_pair_45 (h := h) hh0 hh1,
    d4d_pair_26 (h := h) hh0 hh1,
    d4d_pair_27 (h := h) hh0 hh1,
    d4d_pair_28 (h := h) hh0 hh1,
    d4d_pair_29 (h := h) hh0 hh1,
    d4d_pair_36 (h := h) hh0 hh1,
    d4d_pair_37 (h := h) hh0 hh1,
    d4d_pair_38 (h := h) hh0 hh1,
    d4d_pair_39 (h := h) hh0 hh1,
    d4d_pair_46 (h := h) hh0 hh1,
    d4d_pair_47 (h := h) hh0 hh1,
    d4d_pair_48 (h := h) hh0 hh1,
    d4d_pair_49 (h := h) hh0 hh1,
    d4d_pair_56 (h := h) hh0 hh1,
    d4d_pair_57 (h := h) hh0 hh1,
    d4d_pair_58 (h := h) hh0 hh1,
    d4d_pair_59 (h := h) hh0 hh1,
    d4d_pair_67 (h := h) hh0 hh1,
    d4d_pair_68 (h := h) hh0 hh1,
    d4d_pair_69 (h := h) hh0 hh1,
    d4d_pair_78 (h := h) hh0 hh1,
    d4d_pair_79 (h := h) hh0 hh1,
    d4d_pair_89 (h := h) hh0 hh1
  ]
  unfold d4dEnergyFormula
  ring


end ThomsonTen
