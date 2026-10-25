import ThomsonCertificate.N10StationarityLeftTerm1
import ThomsonNine.IntervalMul

namespace ThomsonTen

open ThomsonNine.Interval
open ThomsonNine.Interval.RatInterval

/-! Lean replay of the second summand of the left endpoint stationarity
expression.  This uses the first summand's exact t² and reciprocal interval. -/

def EL2_m1 : RatInterval := sub (const 1) EL_invT2
def EL2_p3 : RatInterval := add (const 1) (scale 2 (by norm_num) sqrtTwoI)
def EL2_term2 : RatInterval :=
  mulMixed EL2_m1 EL2_p3 (by norm_num [EL2_p3, RatInterval.add,
    RatInterval.scale, RatInterval.const, sqrtTwoI])

theorem EL2_m1_mem : EL2_m1.mem
    (1 - ((63701661910807 / 100000000000000 : ℝ)^2)⁻¹) :=
  mem_sub (by simpa using (mem_const 1)) EL_invT2_mem

theorem EL2_p3_mem : EL2_p3.mem (1 + 2 * Real.sqrt 2) := by
  have h := mem_add (by simpa using (mem_const 1))
    (mem_scale (c := 2) (by norm_num) sqrtTwoI_mem)
  simpa [EL2_p3, RatInterval.add, RatInterval.scale, RatInterval.const] using h

theorem EL2_term2_mem : EL2_term2.mem
    ((1 - ((63701661910807 / 100000000000000 : ℝ)^2)⁻¹) *
      (1 + 2 * Real.sqrt 2)) :=
  mem_mulMixed (by norm_num [EL2_p3, RatInterval.add,
    RatInterval.scale, RatInterval.const, sqrtTwoI]) EL2_m1_mem EL2_p3_mem

theorem EL2_term2_upper_negative : (EL2_term2.hi : ℝ) < 0 := by
  norm_num [EL2_term2, EL2_m1, EL2_p3, EL_invT2, EL_t2, leftT,
    invI, RatInterval.mulMixed, RatInterval.sub, RatInterval.add,
    RatInterval.scale, RatInterval.neg, RatInterval.powNonneg,
    RatInterval.const, sqrtTwoI]

theorem d4dStationarity_left_term2_negative :
    (1 - ((63701661910807 / 100000000000000 : ℝ)^2)⁻¹) *
      (1 + 2 * Real.sqrt 2) < 0 := by
  exact lt_of_le_of_lt EL2_term2_mem.2 EL2_term2_upper_negative

end ThomsonTen
