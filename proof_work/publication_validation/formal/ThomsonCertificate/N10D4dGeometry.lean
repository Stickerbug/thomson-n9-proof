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

end ThomsonTen
