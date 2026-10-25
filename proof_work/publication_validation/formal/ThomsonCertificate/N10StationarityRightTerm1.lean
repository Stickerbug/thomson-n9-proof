import ThomsonCertificate.N10StationarityEndpoint
import Mathlib.Tactic.NormNum

namespace ThomsonTen
open ThomsonNine.Interval
open ThomsonNine.Interval.RatInterval

def ER_t2 : RatInterval := powNonneg rightT (by norm_num [rightT]) 2
def ER_radC : RatInterval := add (const 1) ER_t2
def ER_sqrtC : RatInterval :=
  ⟨(118566022663319894015479118744886073 /
      100000000000000000000000000000000000 : ℚ),
   (118566022663319894015479118744886074 /
      100000000000000000000000000000000000 : ℚ), by norm_num⟩
def ER_invT2 : RatInterval := invI ER_t2
  (by norm_num [ER_t2, rightT, RatInterval.powNonneg])
def ER_invC : RatInterval := invI ER_sqrtC (by norm_num [ER_sqrtC])
def ER_tPlus : RatInterval := add rightT (const 1)
def ER_p1 : RatInterval := mulNonneg ER_tPlus ER_invC
  (by norm_num [ER_tPlus, rightT, RatInterval.add, RatInterval.const])
  (by norm_num [ER_invC, invI, ER_sqrtC])
def ER_p2 : RatInterval := mulNonneg ER_sqrtC ER_invT2
  (by norm_num [ER_sqrtC])
  (by norm_num [ER_invT2, invI, ER_t2, RatInterval.powNonneg, rightT])
def ER_term1 : RatInterval := scale 4 (by norm_num) (sub ER_p1 ER_p2)

theorem ER_t2_mem : ER_t2.mem
    ((7962707738851 / 12500000000000 : ℝ)^2) :=
  mem_powNonneg (by norm_num [rightT]) 2 rightT_mem
theorem ER_radC_mem : ER_radC.mem
    (1 + (7962707738851 / 12500000000000 : ℝ)^2) := by
  simpa [ER_radC] using mem_add (mem_const 1) ER_t2_mem
theorem ER_sqrtC_mem : ER_sqrtC.mem
    (Real.sqrt (1 + (7962707738851 / 12500000000000 : ℝ)^2)) := by
  have h := mem_sqrtI (I := ER_radC)
    (x := 1 + (7962707738851 / 12500000000000 : ℝ)^2)
    (lo := ER_sqrtC.lo) (hi := ER_sqrtC.hi)
    (by norm_num [ER_sqrtC])
    (by norm_num [ER_sqrtC, ER_radC, ER_t2, rightT,
      RatInterval.const, RatInterval.add, RatInterval.powNonneg])
    (by norm_num [ER_sqrtC])
    (by norm_num [ER_sqrtC, ER_radC, ER_t2, rightT,
      RatInterval.const, RatInterval.add, RatInterval.powNonneg])
    (by norm_num [ER_sqrtC]) ER_radC_mem (by positivity)
  simpa [sqrtI, ER_sqrtC] using h
theorem ER_invT2_mem : ER_invT2.mem
    ((7962707738851 / 12500000000000 : ℝ)^2)⁻¹ :=
  mem_invI (by norm_num [ER_t2, rightT, RatInterval.powNonneg]) ER_t2_mem
theorem ER_invC_mem : ER_invC.mem
    (Real.sqrt (1 + (7962707738851 / 12500000000000 : ℝ)^2))⁻¹ :=
  mem_invI (by norm_num [ER_sqrtC]) ER_sqrtC_mem
theorem ER_tPlus_mem : ER_tPlus.mem
    ((7962707738851 / 12500000000000 : ℝ) + 1) := by
  simpa [ER_tPlus] using mem_add rightT_mem (mem_const 1)
theorem ER_p1_mem : ER_p1.mem (((7962707738851 / 12500000000000 : ℝ)+1) *
    (Real.sqrt (1 + (7962707738851 / 12500000000000 : ℝ)^2))⁻¹) :=
  mem_mulNonneg (by norm_num [ER_tPlus, rightT, RatInterval.add, RatInterval.const])
    (by norm_num [ER_invC, invI, ER_sqrtC]) ER_tPlus_mem ER_invC_mem
theorem ER_p2_mem : ER_p2.mem
    (Real.sqrt (1 + (7962707738851 / 12500000000000 : ℝ)^2) *
      ((7962707738851 / 12500000000000 : ℝ)^2)⁻¹) :=
  mem_mulNonneg (by norm_num [ER_sqrtC])
    (by norm_num [ER_invT2, invI, ER_t2, RatInterval.powNonneg, rightT])
    ER_sqrtC_mem ER_invT2_mem
theorem ER_term1_mem : ER_term1.mem (4 * (
    ((7962707738851 / 12500000000000 : ℝ)+1) *
      (Real.sqrt (1 + (7962707738851 / 12500000000000 : ℝ)^2))⁻¹ -
    Real.sqrt (1 + (7962707738851 / 12500000000000 : ℝ)^2) *
      ((7962707738851 / 12500000000000 : ℝ)^2)⁻¹)) := by
  exact mem_scale (by norm_num) (mem_sub ER_p1_mem ER_p2_mem)
theorem ER_term1_upper_negative : (ER_term1.hi : ℝ) < 0 := by
  norm_num [ER_term1, ER_p1, ER_p2, ER_tPlus, ER_invT2, ER_invC,
    ER_t2, ER_sqrtC, rightT, invI, RatInterval.scale, RatInterval.sub,
    RatInterval.add, RatInterval.neg, RatInterval.mulNonneg,
    RatInterval.powNonneg, RatInterval.const]
theorem d4dStationarity_right_term1_negative :
    4 * (((7962707738851 / 12500000000000 : ℝ)+1) /
      Real.sqrt (1 + (7962707738851 / 12500000000000 : ℝ)^2) -
      Real.sqrt (1 + (7962707738851 / 12500000000000 : ℝ)^2) /
        (7962707738851 / 12500000000000 : ℝ)^2) < 0 :=
  lt_of_le_of_lt ER_term1_mem.2 (by simpa [div_eq_mul_inv] using ER_term1_upper_negative)

end ThomsonTen
