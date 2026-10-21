import ThomsonNine.Family
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add

open Real
open ThomsonNine

/-! Probe: derivative of one term of the family energy. -/

example (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun y : ℝ => (Real.sqrt (1 - y ^ 2))⁻¹)
      (x / (Real.sqrt (1 - x ^ 2)) ^ 3) x := by
  have hpos : 0 < 1 - x ^ 2 := by nlinarith
  have hsqrt_ne : Real.sqrt (1 - x ^ 2) ≠ 0 := by positivity
  have hinner : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * x)) x := by
    have h := (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub (hasDerivAt_pow 2 x)
    convert h using 1
    ring
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (1 - x ^ 2))) (1 - x ^ 2) :=
    Real.hasDerivAt_sqrt (ne_of_gt hpos)
  have hcomp : HasDerivAt (fun y : ℝ => Real.sqrt (1 - y ^ 2))
      ((1 / (2 * Real.sqrt (1 - x ^ 2))) * (-(2 * x))) x :=
    hsqrt.comp x hinner
  have hinv := hcomp.inv hsqrt_ne
  convert hinv using 1
  · field_simp
    ring
