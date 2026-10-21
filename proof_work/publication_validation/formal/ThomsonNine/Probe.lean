import ThomsonNine.Statement
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

open scoped BigOperators
open Real
namespace Probe
open ThomsonNine

lemma sqdist_cyl (ρ₁ θ₁ h₁ ρ₂ θ₂ h₂ : ℝ) :
    ‖cyl ρ₁ θ₁ h₁ - cyl ρ₂ θ₂ h₂‖ ^ 2 =
      (ρ₁ * Real.cos θ₁ - ρ₂ * Real.cos θ₂) ^ 2 +
      (ρ₁ * Real.sin θ₁ - ρ₂ * Real.sin θ₂) ^ 2 + (h₁ - h₂) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [cyl, Fin.sum_univ_three]
  ring

lemma cos_two_pi_div_three : Real.cos (2 * π / 3) = -1 / 2 := by
  have h : 2 * π / 3 = π / 3 + π / 3 := by ring
  rw [h, Real.cos_add, Real.cos_pi_div_three, Real.sin_pi_div_three]
  ring_nf

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

noncomputable def p (r : ℝ) : Fin 9 → R3 :=
  ![cyl r 0 (Real.sqrt (1 - r ^ 2)),
    cyl r (2 * π / 3) (Real.sqrt (1 - r ^ 2)),
    cyl r (4 * π / 3) (Real.sqrt (1 - r ^ 2)),
    cyl r 0 (-Real.sqrt (1 - r ^ 2)),
    cyl r (2 * π / 3) (-Real.sqrt (1 - r ^ 2)),
    cyl r (4 * π / 3) (-Real.sqrt (1 - r ^ 2)),
    cyl 1 (π / 3) 0, cyl 1 π 0, cyl 1 (5 * π / 3) 0]

example (r : ℝ) : p r 0 = cyl r 0 (Real.sqrt (1 - r ^ 2)) := by simp [p]

example (r : ℝ) : candidate r 7 = p r 7 := by
  simp [candidate, p]
  ring_nf

example (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 0 - p r 1‖ ^ 2 = (Real.sqrt 3 * r) ^ 2 := by
  simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three]
  ring_nf
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

example (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 0 - p r 3‖ ^ 2 = (2 * Real.sqrt (1 - r ^ 2)) ^ 2 := by
  simp [p, sqdist_cyl]
  ring

example (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 0 - p r 4‖ ^ 2 = (Real.sqrt (4 - r ^ 2)) ^ 2 := by
  simp [p, sqdist_cyl, cos_two_pi_div_three, sin_two_pi_div_three]
  rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 4 - r ^ 2)]
  ring

example (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 6 - p r 7‖ ^ 2 = (Real.sqrt 3) ^ 2 := by
  simp [p, sqdist_cyl, cos_pi_div_three, sin_pi_div_three]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  ring

example (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 0 - p r 6‖ ^ 2 = (Real.sqrt (2 - r)) ^ 2 := by
  simp [p, sqdist_cyl, cos_pi_div_three, sin_pi_div_three]
  rw [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 2 - r)]
  ring

example (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖p r 0 - p r 7‖ ^ 2 = (Real.sqrt (2 + 2 * r)) ^ 2 := by
  simp [p, sqdist_cyl, cos_pi_div_three, sin_pi_div_three]
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + 2 * r)]
  ring

end Probe
