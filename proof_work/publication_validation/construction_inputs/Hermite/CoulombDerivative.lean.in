import ThomsonNine.ActualHermite
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv

-- Isolated source: Hermite.CoulombDerivative
noncomputable section
namespace ThomsonNine.ActualHermite

def coulomb (t : ℝ) : ℝ := (Real.sqrt (2-2*t))⁻¹

theorem coulomb_derivative (x : ℝ) (hx : x<1) : HasDerivAt coulomb ((coulomb x)^3) x := by
  have hp : 0<2-2*x := by linarith
  have hs : Real.sqrt (2-2*x)≠0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  have hbase : HasDerivAt (fun y : ℝ => 2-2*y) (-2) x := by
    convert (hasDerivAt_const x (2 : ℝ)).sub ((hasDerivAt_id' x).const_mul 2) using 1 <;> norm_num
  have h := (hbase.sqrt (ne_of_gt hp)).inv hs
  convert h using 1
  · funext y
    simp only [coulomb,Pi.inv_apply,mul_comm]
  · simp only [coulomb]
    field_simp [hs]
end ThomsonNine.ActualHermite
