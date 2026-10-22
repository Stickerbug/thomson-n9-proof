import ThomsonNine.SparseTranslation

noncomputable section
namespace ThomsonNine.Interval.RatInterval

/-- A rational square comparison encloses the nonnegative real square root. -/
theorem mem_sqrt_of_bounds {I K : RatInterval} {x : ℝ}
    (hx : I.mem x) (hK : 0 ≤ K.lo)
    (hlo : K.lo^2 ≤ I.lo) (hhi : I.hi ≤ K.hi^2) : K.mem (Real.sqrt x) := by
  have hk0 : (0 : ℝ) ≤ K.lo := by exact_mod_cast hK
  have hk1 : (0 : ℝ) ≤ K.hi := by exact_mod_cast hK.trans K.h
  have hl : (K.lo : ℝ)^2 ≤ (I.lo : ℝ) := by exact_mod_cast hlo
  have hh : (I.hi : ℝ) ≤ (K.hi : ℝ)^2 := by exact_mod_cast hhi
  have hx0 : 0 ≤ x := (sq_nonneg (K.lo : ℝ)).trans (hl.trans hx.1)
  have hs := Real.sq_sqrt hx0
  have hp := Real.sqrt_nonneg x
  constructor <;> nlinarith [hx.1,hx.2]
end ThomsonNine.Interval.RatInterval
