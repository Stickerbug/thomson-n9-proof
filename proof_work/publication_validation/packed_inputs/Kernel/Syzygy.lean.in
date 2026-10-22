import Kernel.Syzygy00
import Kernel.Syzygy01
import Kernel.Syzygy02
import Kernel.Syzygy03
import Kernel.Syzygy04
import Kernel.Syzygy05
import Kernel.Syzygy06
import Kernel.Syzygy07
import Kernel.Syzygy08
import Kernel.Syzygy09
import Kernel.Syzygy10
import Mathlib.Tactic.FinCases

noncomputable section
namespace ThomsonNine.ActualKernel.Syzygy
open Polynomial ThomsonNine.RationalListPolynomial ThomsonNine.ExactPolynomial
open scoped BigOperators

theorem p_zero (k i : Fin 11) : dotNum p k i=[] := by
  fin_cases k
  · exact p_zero_00 i
  · exact p_zero_01 i
  · exact p_zero_02 i
  · exact p_zero_03 i
  · exact p_zero_04 i
  · exact p_zero_05 i
  · exact p_zero_06 i
  · exact p_zero_07 i
  · exact p_zero_08 i
  · exact p_zero_09 i
  · exact p_zero_10 i

theorem c_zero (k i : Fin 11) : dotNum c k i=[] := by
  fin_cases k
  · exact c_zero_00 i
  · exact c_zero_01 i
  · exact c_zero_02 i
  · exact c_zero_03 i
  · exact c_zero_04 i
  · exact c_zero_05 i
  · exact c_zero_06 i
  · exact c_zero_07 i
  · exact c_zero_08 i
  · exact c_zero_09 i
  · exact c_zero_10 i

theorem eval_sum (ls : List (List ℚ)) (r : ℝ) :
    (realPolynomial (sum ls)).eval r=(ls.map (fun l => (realPolynomial l).eval r)).sum := by
  rw [sum_sound]
  simp only [eval_listSum,List.map_map,Function.comp_def]

theorem annihilates (f : Fin 11 → Fin 11 → List ℚ) (k i : Fin 11)
    (hz : dotNum f k i=[]) :
    ∑ j : Fin 11, (realPolynomial (f k j)).eval RefinedRadius.radius*N k i j=0 := by
  have h := congrArg (fun l => (realPolynomial l).eval RefinedRadius.radius) hz
  rw [dotNum,eval_sum,List.map_map] at h
  simp only [Function.comp_def,mul_sound,eval_mul] at h
  rw [MonomialSymmetry.finRange_sum] at h
  change (∑ j : Fin 11, (realPolynomial (f k j)).eval RefinedRadius.radius*
    (numValue k i j/denValue k))=0
  simp only [← mul_div_assoc,← Finset.sum_div]
  change (∑ j : Fin 11, (realPolynomial (f k j)).eval RefinedRadius.radius*
    (realPolynomial (numerator k i j)).eval RefinedRadius.radius)/denValue k=0
  rw [h]
  simp

theorem p_annihilates_N (k i : Fin 11) :
    ∑ j : Fin 11, (realPolynomial (p k j)).eval RefinedRadius.radius*N k i j=0 :=
  annihilates p k i (p_zero k i)
theorem c_annihilates_N (k i : Fin 11) :
    ∑ j : Fin 11, (realPolynomial (c k j)).eval RefinedRadius.radius*N k i j=0 :=
  annihilates c k i (c_zero k i)
end ThomsonNine.ActualKernel.Syzygy
