import ThomsonNine.HermiteMinorant

noncomputable section
namespace ThomsonNine.HermiteFactor
open Polynomial
theorem strict_minorant_of_G_positive (H : ℝ[X]) (t : ℝ) (ht : t<1)
    (hG : 0<(G H).eval t) : H.eval t<(Real.sqrt (2-2*t))⁻¹ := by
  have hd : 0<2-2*t := by linarith
  have hs := Real.sqrt_pos.mpr hd
  have hsq := Real.sq_sqrt (le_of_lt hd)
  have hg : (2-2*t)*(H.eval t)^2<1 := by
    simpa only [G,eval_sub,eval_one,eval_mul,eval_C,eval_X,eval_pow,sub_pos] using hG
  have hp : (Real.sqrt (2-2*t)*H.eval t)^2<1 := by
    rw [mul_pow,hsq]
    exact hg
  have hprod : Real.sqrt (2-2*t)*H.eval t<1 := by
    nlinarith [sq_nonneg (Real.sqrt (2-2*t)*H.eval t-1)]
  rw [← one_div,lt_div_iff₀ hs]
  simpa only [mul_comm] using hprod
end ThomsonNine.HermiteFactor
