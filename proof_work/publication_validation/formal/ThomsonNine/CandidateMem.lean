import ThomsonNine.Family
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open scoped BigOperators
open Real

namespace ThomsonNine
namespace Family

lemma norm_cyl_eq_one {ρ θ h : ℝ} (hsum : ρ ^ 2 + h ^ 2 = 1) :
    ‖cyl ρ θ h‖ = 1 := by
  have h2 : ‖cyl ρ θ h‖ ^ 2 = 1 := by
    rw [norm_cyl_sq, hsum]
  rcases sq_eq_one_iff.mp h2 with h1 | h1
  · exact h1
  · have hnn : 0 ≤ ‖cyl ρ θ h‖ := norm_nonneg _
    linarith

lemma norm_p_eq_one (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : Fin 9) :
    ‖p r i‖ = 1 := by
  fin_cases i <;>
    simp [p] <;>
    apply norm_cyl_eq_one <;>
    (have hs : (Real.sqrt (1 - r ^ 2)) ^ 2 = 1 - r ^ 2 :=
      Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 1 - r ^ 2)
     nlinarith)

lemma injective_p (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    Function.Injective (p r) := by
  intro i j hij
  by_contra hne
  have h3 : 0 < Real.sqrt 3 := by positivity
  have hs : 0 < Real.sqrt (1 - r ^ 2) :=
    Real.sqrt_pos.mpr (by nlinarith : (0 : ℝ) < 1 - r ^ 2)
  fin_cases i <;> fin_cases j <;>
    first
      | exact hne rfl
      | (exfalso
         have hz := congrArg (fun v : R3 => v 2) hij
         simp [p, cyl] at hz
         nlinarith)
      | (exfalso
         have hx := congrArg (fun v : R3 => v 0) hij
         have hy := congrArg (fun v : R3 => v 1) hij
         simp [p, cyl, cos_two_pi_div_three, sin_two_pi_div_three,
           cos_four_pi_div_three, sin_four_pi_div_three,
           cos_five_pi_div_three, sin_five_pi_div_three,
           cos_pi_div_three, sin_pi_div_three] at hx hy
         first
           | done
           | nlinarith [h3, hr, hs]
           | (rcases hy with h | h <;> nlinarith [h3, hr, hs])
           | (rcases hx with h | h <;> nlinarith [h3, hr, hs])
           | (rcases hx with h | h <;>
              rcases hy with h' | h' <;> nlinarith [h3, hr, hs]))

lemma candidate_mem_sphere (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    candidate r ∈ SphereConfig 9 := by
  constructor
  · intro i
    rw [candidate_eq_p]
    exact norm_p_eq_one r hr hr1 i
  · rw [candidate_eq_p]
    exact injective_p r hr hr1

end Family
end ThomsonNine
