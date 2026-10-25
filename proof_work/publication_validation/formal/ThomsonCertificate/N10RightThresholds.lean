import ThomsonCertificate.N10RightEndpointFacts

namespace ThomsonTen
open ThomsonNine.Interval
open ThomsonNine.Interval.RatInterval

theorem ER2_m1_lo_gt_three_halves : (-3 / 2 : ℝ) < ER2_m1.lo := by
  norm_num [ER2_m1, ER_invT2, ER_t2, rightT, invI,
    RatInterval.sub, RatInterval.neg, RatInterval.add,
    RatInterval.const, RatInterval.powNonneg]

theorem ER2_term2_lo_eq : (ER2_term2.lo : ℝ) =
    (ER2_m1.lo : ℝ) * (ER2_p3.hi : ℝ) := by
  have hlo : ¬ (0 : ℚ) ≤ ER2_m1.lo := by
    norm_num [ER2_m1, ER_invT2, ER_t2, rightT, invI,
      RatInterval.sub, RatInterval.neg, RatInterval.add,
      RatInterval.const, RatInterval.powNonneg]
  have hhi : ER2_m1.hi ≤ 0 := by
    norm_num [ER2_m1, ER_invT2, ER_t2, rightT, invI,
      RatInterval.sub, RatInterval.neg, RatInterval.add,
      RatInterval.const, RatInterval.powNonneg]
  simp [ER2_term2, RatInterval.mulMixed, hlo, hhi]

theorem ER2_term2_lo_gt_six : (-6 : ℝ) < ER2_term2.lo := by
  rw [ER2_term2_lo_eq]
  have hp : (0 : ℝ) < ER2_p3.hi := by
    norm_num [ER2_p3, sqrtTwoI, RatInterval.add, RatInterval.scale,
      RatInterval.const]
  have hm := ER2_m1_lo_gt_three_halves
  have hq := ER2_p3_hi_lt_four
  nlinarith

end ThomsonTen
