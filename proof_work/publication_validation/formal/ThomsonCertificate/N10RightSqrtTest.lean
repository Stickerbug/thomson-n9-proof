import ThomsonCertificate.N10StationarityRightTerm2
import ThomsonNine.IntervalMul

namespace ThomsonTen
open ThomsonNine.Interval
open ThomsonNine.Interval.RatInterval

def ER3_sqrtTwo : RatInterval :=
  ⟨(1414213562373095048801688724209698078569 /
      1000000000000000000000000000000000000000 : ℚ),
   (1414213562373095048801688724209698078570 /
      1000000000000000000000000000000000000000 : ℚ), by norm_num⟩

theorem ER3_sqrtTwo_mem : ER3_sqrtTwo.mem (Real.sqrt 2) := by
  have hlo : (0 : ℝ) ≤ (ER3_sqrtTwo.lo : ℝ) := by norm_num [ER3_sqrtTwo]
  constructor
  · apply (Real.le_sqrt hlo (by norm_num)).2
    norm_num [ER3_sqrtTwo]
  · apply (Real.sqrt_le_iff).2
    constructor <;> norm_num [ER3_sqrtTwo]

def ER3_t4 : RatInterval := powNonneg ER_t2 (by
  norm_num [ER_t2, rightT, RatInterval.powNonneg]) 2
def ER3_s2t2 : RatInterval := mulNonneg ER3_sqrtTwo ER_t2
  (by norm_num [ER3_sqrtTwo])
  (by norm_num [ER_t2, rightT, RatInterval.powNonneg])
def ER3_radA : RatInterval := add (add ER3_t4 ER3_s2t2) (const 1)
def ER3_radB : RatInterval := add (sub ER3_t4 ER3_s2t2) (const 1)
def ER3_sqrtA : RatInterval :=
  ⟨(1318536928069124102 / 1000000000000000000 : ℚ),
   (1318536928069124103 / 1000000000000000000 : ℚ), by norm_num⟩
def ER3_sqrtB : RatInterval :=
  ⟨(768629753754731916 / 1000000000000000000 : ℚ),
   (768629753754731917 / 1000000000000000000 : ℚ), by norm_num⟩

theorem ER3_radA_lo_sq : (ER3_sqrtA.lo : ℝ)^2 ≤ (ER3_radA.lo : ℝ) := by
  norm_num [ER3_radA, ER3_t4, ER3_s2t2, ER_t2, rightT, ER3_sqrtTwo,
    RatInterval.powNonneg, RatInterval.mulNonneg, RatInterval.add,
    RatInterval.const, ER3_sqrtA]

theorem ER3_radA_hi_sq : (ER3_radA.hi : ℝ) ≤ (ER3_sqrtA.hi : ℝ)^2 := by
  norm_num [ER3_radA, ER3_t4, ER3_s2t2, ER_t2, rightT, ER3_sqrtTwo,
    RatInterval.powNonneg, RatInterval.mulNonneg, RatInterval.add,
    RatInterval.const, ER3_sqrtA]

theorem ER3_radB_hi_sq : (ER3_radB.hi : ℝ) ≤ (ER3_sqrtB.hi : ℝ)^2 := by
  norm_num [ER3_radB, ER3_t4, ER3_s2t2, ER_t2, rightT, ER3_sqrtTwo,
    RatInterval.powNonneg, RatInterval.mulNonneg, RatInterval.sub,
    RatInterval.neg, RatInterval.add, RatInterval.const, ER3_sqrtB]

theorem ER3_radB_lo_sq : (ER3_sqrtB.lo : ℝ)^2 ≤ (ER3_radB.lo : ℝ) := by
  norm_num [ER3_radB, ER3_t4, ER3_s2t2, ER_t2, rightT, ER3_sqrtTwo,
    RatInterval.powNonneg, RatInterval.mulNonneg, RatInterval.sub,
    RatInterval.neg, RatInterval.add, RatInterval.const, ER3_sqrtB]

end ThomsonTen
