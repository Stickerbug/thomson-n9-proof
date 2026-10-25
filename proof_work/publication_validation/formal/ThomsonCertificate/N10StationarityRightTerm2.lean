import ThomsonCertificate.N10StationarityRightTerm1
import ThomsonNine.IntervalMul

namespace ThomsonTen
open ThomsonNine.Interval
open ThomsonNine.Interval.RatInterval

def ER2_m1 : RatInterval := sub (const 1) ER_invT2
def ER2_p3 : RatInterval := add (const 1) (scale 2 (by norm_num) sqrtTwoI)
def ER2_term2 : RatInterval :=
  mulMixed ER2_m1 ER2_p3 (by norm_num [ER2_p3, RatInterval.add,
    RatInterval.scale, RatInterval.const, sqrtTwoI])

theorem ER2_m1_mem : ER2_m1.mem
    (1 - ((7962707738851 / 12500000000000 : ℝ)^2)⁻¹) :=
  mem_sub (by simpa using (mem_const 1)) ER_invT2_mem
theorem ER2_p3_mem : ER2_p3.mem (1 + 2 * Real.sqrt 2) := by
  have h := mem_add (by simpa using (mem_const 1))
    (mem_scale (c := 2) (by norm_num) sqrtTwoI_mem)
  simpa [ER2_p3, RatInterval.add, RatInterval.scale, RatInterval.const] using h
theorem ER2_term2_mem : ER2_term2.mem
    ((1 - ((7962707738851 / 12500000000000 : ℝ)^2)⁻¹) *
      (1 + 2 * Real.sqrt 2)) :=
  mem_mulMixed (by norm_num [ER2_p3, RatInterval.add,
    RatInterval.scale, RatInterval.const, sqrtTwoI]) ER2_m1_mem ER2_p3_mem
theorem ER2_term2_upper_negative : (ER2_term2.hi : ℝ) < 0 := by
  norm_num [ER2_term2, ER2_m1, ER2_p3, ER_invT2, ER_t2, rightT,
    invI, RatInterval.mulMixed, RatInterval.sub, RatInterval.add,
    RatInterval.scale, RatInterval.neg, RatInterval.powNonneg,
    RatInterval.const, sqrtTwoI]
theorem d4dStationarity_right_term2_negative :
    (1 - ((7962707738851 / 12500000000000 : ℝ)^2)⁻¹) *
      (1 + 2 * Real.sqrt 2) < 0 :=
  lt_of_le_of_lt ER2_term2_mem.2 ER2_term2_upper_negative

end ThomsonTen
