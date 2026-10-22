import ThomsonNine.GramBoundary
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv

noncomputable section
namespace ThomsonNine.GramGraph
def radical (v t : ℝ) : ℝ := Real.sqrt ((1-v^2)*(1-t^2))
def slope (v t : ℝ) : ℝ := t+v*(1-t^2)/radical v t
def curvatureVV (v t : ℝ) : ℝ := (1-t^2)/((1-v^2)*radical v t)
def curvatureVT (v t : ℝ) : ℝ := 1-v*t/radical v t

theorem radical_swap (v t : ℝ) : radical v t=radical t v := by
  unfold radical
  rw [mul_comm]
theorem radical_pos {v t : ℝ} (hv : 0<1-v^2) (ht : 0<1-t^2) : 0<radical v t :=
  Real.sqrt_pos.mpr (mul_pos hv ht)
theorem radical_sq {v t : ℝ} (hv : 0<1-v^2) (ht : 0<1-t^2) :
    (radical v t)^2=(1-v^2)*(1-t^2) := Real.sq_sqrt (le_of_lt (mul_pos hv ht))

theorem radical_derivative (V T : ℝ → ℝ) (y z s : ℝ)
    (hV : HasDerivAt V y s) (hT : HasDerivAt T z s)
    (hv : 0<1-(V s)^2) (ht : 0<1-(T s)^2) :
    HasDerivAt (fun q => radical (V q) (T q))
      (-(V s*y*(1-(T s)^2)+T s*z*(1-(V s)^2))/radical (V s) (T s)) s := by
  have h := (((hasDerivAt_const s (1 : ℝ)).sub (hV.pow 2)).mul
    ((hasDerivAt_const s (1 : ℝ)).sub (hT.pow 2))).sqrt (ne_of_gt (mul_pos hv ht))
  have hs := ne_of_gt (radical_pos hv ht)
  convert h using 1
  · rfl
  · change -(V s*y*(1-(T s)^2)+T s*z*(1-(V s)^2))/radical (V s) (T s)=
      ((0-2*(V s)^1*y)*(1-(T s)^2)+(1-(V s)^2)*(0-2*(T s)^1*z))/(2*radical (V s) (T s))
    simp only [pow_one]
    field_simp
    ring

theorem lowerGraph_derivative (V T : ℝ → ℝ) (y z s : ℝ)
    (hV : HasDerivAt V y s) (hT : HasDerivAt T z s)
    (hv : 0<1-(V s)^2) (ht : 0<1-(T s)^2) :
    HasDerivAt (fun q => LocalLDL.lowerGraph (V q) (T q))
      (slope (V s) (T s)*y+slope (T s) (V s)*z) s := by
  have h := (hV.mul hT).sub (radical_derivative V T y z s hV hT hv ht)
  have hs := ne_of_gt (radical_pos hv ht)
  convert h using 1
  · rfl
  · dsimp only [slope]
    rw [radical_swap (T s) (V s)]
    field_simp
    ring

theorem slope_derivative (V T : ℝ → ℝ) (y z s : ℝ)
    (hV : HasDerivAt V y s) (hT : HasDerivAt T z s)
    (hv : 0<1-(V s)^2) (ht : 0<1-(T s)^2) :
    HasDerivAt (fun q => slope (V q) (T q))
      (curvatureVV (V s) (T s)*y+curvatureVT (V s) (T s)*z) s := by
  have hs := ne_of_gt (radical_pos hv ht)
  have h := hT.add ((hV.mul ((hasDerivAt_const s (1 : ℝ)).sub (hT.pow 2))).div
    (radical_derivative V T y z s hV hT hv ht) hs)
  convert h using 1
  · rfl
  · dsimp only [curvatureVV,curvatureVT,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply]
    norm_num only [Nat.cast_ofNat,pow_one]
    field_simp
    linear_combination (V s*(V s*y*(1-(T s)^2)+T s*z*(1-(V s)^2)))*radical_sq hv ht
end ThomsonNine.GramGraph
