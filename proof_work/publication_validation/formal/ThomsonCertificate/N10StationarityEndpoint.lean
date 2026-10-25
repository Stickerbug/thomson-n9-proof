import ThomsonCertificate.N10CandidateInterval
import ThomsonNine.Interval
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace ThomsonTen
open ThomsonNine.Interval
open ThomsonNine.Interval.RatInterval

/-!
# Lean replay primitives for the n=10 stationarity endpoint certificate

The external certificate is generated with exact rational outward rounding.  This
file supplies the corresponding sound Lean primitives: reciprocal intervals and
square-root intervals.  The endpoint-specific arithmetic can then be generated
from these primitives without introducing a floating-point axiom.
-/

/-- Reciprocal of a strictly positive rational interval. -/
def invI (I : RatInterval) (h : 0 < I.lo) : RatInterval :=
  ⟨1 / I.hi, 1 / I.lo, by
    exact one_div_le_one_div_of_le h I.h⟩

theorem mem_invI {I : RatInterval} {x : ℝ} (h : 0 < I.lo) (hx : I.mem x) :
    (invI I h).mem x⁻¹ := by
  have hlo : (0 : ℝ) < (I.lo : ℝ) := by exact_mod_cast h
  have hhi : (0 : ℝ) < (I.hi : ℝ) := lt_of_lt_of_le hlo (by exact_mod_cast I.h)
  have hx0 : 0 < x := lt_of_lt_of_le hlo hx.1
  constructor
  · change ((1 / I.hi : ℚ) : ℝ) ≤ x⁻¹
    simpa [one_div] using (one_div_le_one_div_of_le hx0 hx.2)
  · change x⁻¹ ≤ ((1 / I.lo : ℚ) : ℝ)
    simpa [one_div] using (one_div_le_one_div_of_le hlo hx.1)

/-- A rational interval intended to contain a nonnegative square root. -/
def sqrtI (lo hi : ℚ) (h : lo ≤ hi) : RatInterval := ⟨lo, hi, h⟩

theorem mem_sqrtI {I : RatInterval} {x : ℝ} {lo hi : ℚ}
    (hlo : 0 ≤ lo) (hlo_sq : lo ^ 2 ≤ I.lo)
    (hhi : 0 ≤ hi) (hhi_sq : I.hi ≤ hi ^ 2)
    (hlo_hi : lo ≤ hi) (hx : I.mem x) (hx_nonneg : 0 ≤ x) :
    (sqrtI lo hi hlo_hi).mem (Real.sqrt x) := by
  constructor
  · apply (Real.le_sqrt (by exact_mod_cast hlo) hx_nonneg).2
    have hxl : (I.lo : ℝ) ≤ x := hx.1
    have hsq : ((lo ^ 2 : ℚ) : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast hlo_sq
    simpa [sqrtI, Rat.cast_pow] using le_trans hsq hxl
  · apply (Real.sqrt_le_iff).2
    constructor
    · exact_mod_cast hhi
    · have hxu : x ≤ (I.hi : ℝ) := hx.2
      have hsq : (I.hi : ℝ) ≤ ((hi ^ 2 : ℚ) : ℝ) := by exact_mod_cast hhi_sq
      simpa [sqrtI, Rat.cast_pow] using le_trans hxu hsq

/-- Exact rational enclosure for √2 used by both endpoint certificates. -/
def sqrtTwoI : RatInterval :=
  ⟨(90509667991878083123308078349420677028459 /
      64000000000000000000000000000000000000000 : ℚ),
   (353553390593273762200422181052424519642417969 /
      250000000000000000000000000000000000000000000 : ℚ), by norm_num⟩

theorem sqrtTwoI_mem : sqrtTwoI.mem (Real.sqrt 2) := by
  have hlo : (0 : ℝ) ≤ (sqrtTwoI.lo : ℝ) := by norm_num [sqrtTwoI]
  constructor
  · apply (Real.le_sqrt hlo (by norm_num)).2
    norm_num [sqrtTwoI]
  · apply (Real.sqrt_le_iff).2
    constructor <;> norm_num [sqrtTwoI]

/-- The left endpoint parameter is represented exactly as a rational constant. -/
def leftT : RatInterval :=
  ⟨(63701661910807 / 100000000000000 : ℚ),
   (63701661910807 / 100000000000000 : ℚ), by norm_num⟩

theorem leftT_mem : leftT.mem (63701661910807 / 100000000000000 : ℝ) := by
  norm_num [leftT, RatInterval.mem]

/-- The right endpoint parameter is represented exactly as a rational constant. -/
def rightT : RatInterval :=
  ⟨(7962707738851 / 12500000000000 : ℚ),
   (7962707738851 / 12500000000000 : ℚ), by norm_num⟩

-- The equality endpoint is exposed separately to avoid decimal parsing ambiguity.
theorem rightT_mem : rightT.mem (7962707738851 / 12500000000000 : ℝ) := by
  norm_num [rightT, RatInterval.mem]

end ThomsonTen
