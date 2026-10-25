import ThomsonCertificate.N10StationarityLeftTerm2
import ThomsonNine.IntervalMul

namespace ThomsonTen

open ThomsonNine.Interval
open ThomsonNine.Interval.RatInterval

/-! Exact interval sublayer for the algebraic numerators occurring in the
third left-endpoint stationarity term.  The square-root inverse cubes and the
final sign are separate obligations. -/

def EL3_sqrtTwo : RatInterval :=
  ⟨(1414213562373095048801688724209698078569 /
      1000000000000000000000000000000000000000 : ℚ),
   (1414213562373095048801688724209698078570 /
      1000000000000000000000000000000000000000 : ℚ), by norm_num⟩

theorem EL3_sqrtTwo_mem : EL3_sqrtTwo.mem (Real.sqrt 2) := by
  have hlo : (0 : ℝ) ≤ (EL3_sqrtTwo.lo : ℝ) := by norm_num [EL3_sqrtTwo]
  constructor
  · apply (Real.le_sqrt hlo (by norm_num)).2
    norm_num [EL3_sqrtTwo]
  · apply (Real.sqrt_le_iff).2
    constructor <;> norm_num [EL3_sqrtTwo]

def EL3_pbase : RatInterval :=
  mulNonneg (add (const 1) EL_t2) leftT
    (by norm_num [EL_t2, leftT, RatInterval.add, RatInterval.const,
      RatInterval.powNonneg])
    (by norm_num [leftT])
def EL3_abase : RatInterval :=
  add (scale 2 (by norm_num) EL_t2) EL3_sqrtTwo
def EL3_bbase : RatInterval :=
  sub (scale 2 (by norm_num) EL_t2) EL3_sqrtTwo
def EL3_anum : RatInterval :=
  mulNonneg EL3_pbase EL3_abase
    (by norm_num [EL3_pbase, RatInterval.mulNonneg, RatInterval.add,
      RatInterval.const, EL_t2, leftT, RatInterval.powNonneg])
    (by norm_num [EL3_abase, RatInterval.add, RatInterval.scale,
      RatInterval.const, EL_t2, leftT, RatInterval.powNonneg,
      EL3_sqrtTwo])
def EL3_bnum : RatInterval :=
  mulMixed EL3_bbase EL3_pbase
    (by norm_num [EL3_pbase, RatInterval.mulNonneg, RatInterval.add,
      RatInterval.const, EL_t2, leftT, RatInterval.powNonneg])

theorem EL3_pbase_mem : EL3_pbase.mem
    ((1 + (63701661910807 / 100000000000000 : ℝ)^2) *
      (63701661910807 / 100000000000000 : ℝ)) := by
  exact mem_mulNonneg
    (by norm_num [EL_t2, leftT, RatInterval.add, RatInterval.const,
      RatInterval.powNonneg]) (by norm_num [leftT])
    (mem_add (by simpa using (mem_const 1)) EL_t2_mem) leftT_mem

theorem EL3_abase_mem : EL3_abase.mem
    (2 * (63701661910807 / 100000000000000 : ℝ)^2 + Real.sqrt 2) := by
  have h := mem_add (mem_scale (c := 2) (by norm_num) EL_t2_mem)
    EL3_sqrtTwo_mem
  simpa [EL3_abase, RatInterval.add, RatInterval.scale] using h

theorem EL3_bbase_mem : EL3_bbase.mem
    (2 * (63701661910807 / 100000000000000 : ℝ)^2 - Real.sqrt 2) := by
  exact mem_sub (mem_scale (c := 2) (by norm_num) EL_t2_mem)
    EL3_sqrtTwo_mem

theorem EL3_anum_mem : EL3_anum.mem
    (((1 + (63701661910807 / 100000000000000 : ℝ)^2) *
      (63701661910807 / 100000000000000 : ℝ)) *
      (2 * (63701661910807 / 100000000000000 : ℝ)^2 + Real.sqrt 2)) :=
  mem_mulNonneg
    (by norm_num [EL3_pbase, RatInterval.mulNonneg, RatInterval.add,
      RatInterval.const, EL_t2, leftT, RatInterval.powNonneg])
    (by norm_num [EL3_abase, RatInterval.add, RatInterval.scale,
      RatInterval.const, EL_t2, leftT, RatInterval.powNonneg,
      EL3_sqrtTwo]) EL3_pbase_mem EL3_abase_mem

theorem EL3_bnum_mem : EL3_bnum.mem
    ((2 * (63701661910807 / 100000000000000 : ℝ)^2 - Real.sqrt 2) *
      ((1 + (63701661910807 / 100000000000000 : ℝ)^2) *
      (63701661910807 / 100000000000000 : ℝ))) :=
  mem_mulMixed
    (by norm_num [EL3_pbase, RatInterval.mulNonneg, RatInterval.add,
      RatInterval.const, EL_t2, leftT, RatInterval.powNonneg])
    EL3_bbase_mem EL3_pbase_mem

end ThomsonTen
