import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.NormNum

example : HasDerivAt (fun t : ℝ => 1 + t) 1 0 :=
  (hasDerivAt_id (0:ℝ)).const_add 1

example : HasDerivAt (fun t : ℝ => (1 + t)⁻¹) (-1) 0 := by
  let g : ℝ → ℝ := fun t => 1 + t
  have hlin : HasDerivAt g 1 0 := by
    show HasDerivAt (fun t : ℝ => 1 + t) 1 0
    exact (hasDerivAt_id (0:ℝ)).const_add 1
  have h1 : HasDerivAt (fun y : ℝ => y⁻¹) (-1) (g 0) := by
    show HasDerivAt (fun y : ℝ => y⁻¹) (-1) (1 + 0)
    have h := hasDerivAt_inv (x := (1:ℝ)) (by norm_num)
    convert h using 1
    norm_num
  have h := h1.comp hlin
  simpa [g, Function.comp_def, mul_one] using h
