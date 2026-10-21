import ThomsonNine.Family
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

open scoped BigOperators InnerProductSpace
open Real

namespace ThomsonNine
open ThomsonNine.Family

/-! The six pairwise inner-product values of the one-parameter candidate family.

These are the inner-product counterparts of the contact-equation constants
`A = 1 - 3r²/2`, `B = 2r² - 1`, `C = r²/2 - 1`, `D = -1/2`, `F = r/2`, `G = -r`
used in the analytic proof candidate. -/

lemma inner_p_T_T (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ⟪p r 0, p r 1⟫_ℝ = 1 - 3 * r ^ 2 / 2 := by
  simp [p, PiLp.inner_apply, Fin.sum_univ_three, cyl, cos_two_pi_div_three,
    sin_two_pi_div_three]
  try simp only [← pow_two, Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
  try ring

lemma inner_p_T_B_same (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ⟪p r 0, p r 3⟫_ℝ = 2 * r ^ 2 - 1 := by
  simp [p, PiLp.inner_apply, Fin.sum_univ_three, cyl]
  try simp only [← pow_two, Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
  try ring

lemma inner_p_T_B_diff (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ⟪p r 0, p r 4⟫_ℝ = r ^ 2 / 2 - 1 := by
  simp [p, PiLp.inner_apply, Fin.sum_univ_three, cyl, cos_two_pi_div_three,
    sin_two_pi_div_three]
  try simp only [← pow_two, Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)]
  try ring

lemma inner_p_E_E (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ⟪p r 6, p r 7⟫_ℝ = -1 / 2 := by
  simp [p, PiLp.inner_apply, Fin.sum_univ_three, cyl, cos_pi_div_three,
    sin_pi_div_three, cos_pi, sin_pi]
  try ring

lemma inner_p_ring_E_adj (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ⟪p r 0, p r 6⟫_ℝ = r / 2 := by
  simp [p, PiLp.inner_apply, Fin.sum_univ_three, cyl, cos_pi_div_three,
    sin_pi_div_three]
  try ring

lemma inner_p_ring_E_opp (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ⟪p r 0, p r 7⟫_ℝ = -r := by
  simp [p, PiLp.inner_apply, Fin.sum_univ_three, cyl, cos_pi, sin_pi]
  try ring

end ThomsonNine
