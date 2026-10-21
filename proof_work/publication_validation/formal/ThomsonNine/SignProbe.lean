import ThomsonNine.Derivative
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open ThomsonNine.Family
namespace Probe

lemma half_neg : familyEnergyDeriv (1 / 2) < 0 := by
  have h1 : (1 : ℝ) - (1 / 2) ^ 2 = 3 / 4 := by norm_num
  have h2 : (4 : ℝ) - (1 / 2) ^ 2 = 15 / 4 := by norm_num
  have h3 : (2 : ℝ) - 1 / 2 = 3 / 2 := by norm_num
  have h4 : (2 : ℝ) + 2 * (1 / 2) = 3 := by norm_num
  have h5 : (1 / 2 : ℝ) ^ 2 = 1 / 4 := by norm_num
  simp only [familyEnergyDeriv, h1, h2, h3, h4, h5]
  have y34 : (0.86 : ℝ) < Real.sqrt (3 / 4) := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have y154 : (1.93 : ℝ) < Real.sqrt (15 / 4) := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have y32 : (1.22 : ℝ) < Real.sqrt (3 / 2) := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have x3lo : (1.7 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have x3hi : Real.sqrt 3 < 1.75 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have b1 : -2 * Real.sqrt 3 / (1 / 4 : ℝ) < -13.6 := by
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 1 / 4)]
    nlinarith
  have b2 : 3 * (1 / 2) / (2 * (Real.sqrt (3 / 4)) ^ 3) < 1.2 := by
    have hy : (0 : ℝ) < Real.sqrt (3 / 4) := by positivity
    have hc : (0.86 : ℝ) ^ 3 < (Real.sqrt (3 / 4)) ^ 3 := by
      exact pow_lt_pow_left₀ y34 (by norm_num) (by norm_num)
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (Real.sqrt (3 / 4)) ^ 3)]
    nlinarith
  have b3 : 6 * (1 / 2) / (Real.sqrt (15 / 4)) ^ 3 < 0.5 := by
    have hy : (0 : ℝ) < Real.sqrt (15 / 4) := by positivity
    have hc : (1.93 : ℝ) ^ 3 < (Real.sqrt (15 / 4)) ^ 3 := by
      exact pow_lt_pow_left₀ y154 (by norm_num) (by norm_num)
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (Real.sqrt (15 / 4)) ^ 3)]
    nlinarith
  have b4 : 6 / (Real.sqrt (3 / 2)) ^ 3 < 3.4 := by
    have hy : (0 : ℝ) < Real.sqrt (3 / 2) := by positivity
    have hc : (1.22 : ℝ) ^ 3 < (Real.sqrt (3 / 2)) ^ 3 := by
      exact pow_lt_pow_left₀ y32 (by norm_num) (by norm_num)
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (Real.sqrt (3 / 2)) ^ 3)]
    nlinarith
  have b5 : -(6 / (Real.sqrt 3) ^ 3) < -1.1 := by
    rw [← neg_div]
    have hy : (0 : ℝ) < Real.sqrt 3 := by positivity
    have hc : (Real.sqrt 3) ^ 3 < (1.75 : ℝ) ^ 3 := by
      exact pow_lt_pow_left₀ x3hi (by positivity) (by norm_num)
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (Real.sqrt 3) ^ 3)]
    nlinarith
  linarith

end Probe
