import ThomsonCertificate.N10StationarityEndpoint
import Mathlib.Tactic.NormNum

namespace ThomsonTen

open ThomsonNine.Interval
open ThomsonNine.Interval.RatInterval

def EL_t2 : RatInterval := RatInterval.powNonneg leftT (by norm_num [leftT]) 2
def EL_radC : RatInterval := RatInterval.add (RatInterval.const 1) EL_t2
def EL_sqrtC : RatInterval :=
  ⟨(118566022663319356748 / 100000000000000000000 : ℚ),
   (118566022663319356749 / 100000000000000000000 : ℚ), by norm_num⟩
def EL_invT2 : RatInterval := invI EL_t2 (by
  norm_num [EL_t2, leftT, RatInterval.powNonneg])
def EL_invC : RatInterval := invI EL_sqrtC (by norm_num [EL_sqrtC])
def EL_tPlus : RatInterval := RatInterval.add leftT (RatInterval.const 1)
def EL_p1 : RatInterval := RatInterval.mulNonneg EL_tPlus EL_invC
  (by norm_num [EL_tPlus, leftT, RatInterval.add, RatInterval.const])
  (by norm_num [EL_invC, invI, EL_sqrtC])
def EL_p2 : RatInterval := RatInterval.mulNonneg EL_sqrtC EL_invT2
  (by norm_num [EL_sqrtC])
  (by norm_num [EL_invT2, invI, EL_t2, RatInterval.powNonneg, leftT])
def EL_term1 : RatInterval := RatInterval.scale 4 (by norm_num)
  (RatInterval.sub EL_p1 EL_p2)

theorem EL_t2_mem : EL_t2.mem
    ((63701661910807 / 100000000000000 : ℝ)^2) := by
  exact RatInterval.mem_powNonneg (by norm_num [leftT]) 2 leftT_mem

theorem EL_radC_mem : EL_radC.mem
    (1 + (63701661910807 / 100000000000000 : ℝ)^2) := by
  simpa [EL_radC] using RatInterval.mem_add
    (RatInterval.mem_const 1) EL_t2_mem

theorem EL_sqrtC_mem : EL_sqrtC.mem
    (Real.sqrt (1 + (63701661910807 / 100000000000000 : ℝ)^2)) := by
  have h := mem_sqrtI (I := EL_radC)
    (x := 1 + (63701661910807 / 100000000000000 : ℝ)^2)
    (lo := EL_sqrtC.lo) (hi := EL_sqrtC.hi)
    (by norm_num [EL_sqrtC])
    (by norm_num [EL_sqrtC, EL_radC, EL_t2, leftT,
      RatInterval.const, RatInterval.add, RatInterval.powNonneg])
    (by norm_num [EL_sqrtC])
    (by norm_num [EL_sqrtC, EL_radC, EL_t2, leftT,
      RatInterval.const, RatInterval.add, RatInterval.powNonneg])
    (by norm_num [EL_sqrtC]) EL_radC_mem (by positivity)
  simpa [sqrtI, EL_sqrtC] using h

theorem EL_invT2_mem : EL_invT2.mem
    ((63701661910807 / 100000000000000 : ℝ)^2)⁻¹ :=
  mem_invI (by norm_num [EL_t2, leftT, RatInterval.powNonneg]) EL_t2_mem

theorem EL_invC_mem : EL_invC.mem
    (Real.sqrt (1 + (63701661910807 / 100000000000000 : ℝ)^2))⁻¹ :=
  mem_invI (by norm_num [EL_sqrtC]) EL_sqrtC_mem

theorem EL_tPlus_mem : EL_tPlus.mem
    ((63701661910807 / 100000000000000 : ℝ) + 1) := by
  simpa [EL_tPlus] using RatInterval.mem_add leftT_mem
    (RatInterval.mem_const 1)

theorem EL_p1_mem : EL_p1.mem
    (((63701661910807 / 100000000000000 : ℝ) + 1) *
      (Real.sqrt (1 + (63701661910807 / 100000000000000 : ℝ)^2))⁻¹) :=
  RatInterval.mem_mulNonneg
    (by norm_num [EL_tPlus, leftT, RatInterval.add, RatInterval.const])
    (by norm_num [EL_invC, invI, EL_sqrtC]) EL_tPlus_mem EL_invC_mem

theorem EL_p2_mem : EL_p2.mem
    (Real.sqrt (1 + (63701661910807 / 100000000000000 : ℝ)^2) *
      ((63701661910807 / 100000000000000 : ℝ)^2)⁻¹) :=
  RatInterval.mem_mulNonneg (by norm_num [EL_sqrtC])
    (by norm_num [EL_invT2, invI, EL_t2, RatInterval.powNonneg, leftT])
    EL_sqrtC_mem EL_invT2_mem

theorem EL_term1_mem : EL_term1.mem (4 * (
    ((63701661910807 / 100000000000000 : ℝ) + 1) *
      (Real.sqrt (1 + (63701661910807 / 100000000000000 : ℝ)^2))⁻¹ -
    Real.sqrt (1 + (63701661910807 / 100000000000000 : ℝ)^2) *
      ((63701661910807 / 100000000000000 : ℝ)^2)⁻¹)) := by
  exact RatInterval.mem_scale (by norm_num)
    (RatInterval.mem_sub EL_p1_mem EL_p2_mem)

theorem EL_term1_upper_negative : (EL_term1.hi : ℝ) < 0 := by
  norm_num [EL_term1, EL_p1, EL_p2, EL_tPlus, EL_invT2, EL_invC,
    EL_t2, EL_sqrtC, leftT, invI, RatInterval.scale,
    RatInterval.sub, RatInterval.add, RatInterval.neg,
    RatInterval.mulNonneg, RatInterval.powNonneg, RatInterval.const]

theorem d4dStationarity_left_term1_negative :
    4 * (((63701661910807 / 100000000000000 : ℝ) + 1) /
      Real.sqrt (1 + (63701661910807 / 100000000000000 : ℝ)^2) -
      Real.sqrt (1 + (63701661910807 / 100000000000000 : ℝ)^2) /
        (63701661910807 / 100000000000000 : ℝ)^2) < 0 := by
  have hm := EL_term1_mem
  exact lt_of_le_of_lt hm.2 (by simpa [div_eq_mul_inv] using EL_term1_upper_negative)

end ThomsonTen
