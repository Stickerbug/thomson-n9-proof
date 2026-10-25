import ThomsonCertificate.N10StationarityRightTerm2
namespace ThomsonTen
open ThomsonNine.Interval
open ThomsonNine.Interval.RatInterval

theorem sqrtTwoI_hi_lt_three_halves : (sqrtTwoI.hi : ℝ) < (3 / 2 : ℝ) := by
  norm_num [sqrtTwoI]

theorem ER2_p3_hi_eq : ER2_p3.hi = 1 + 2 * sqrtTwoI.hi := by rfl

theorem ER2_p3_hi_lt_four : (ER2_p3.hi : ℝ) < 4 := by
  rw [ER2_p3_hi_eq]
  have h := sqrtTwoI_hi_lt_three_halves
  norm_num at h ⊢
  linarith

end ThomsonTen
