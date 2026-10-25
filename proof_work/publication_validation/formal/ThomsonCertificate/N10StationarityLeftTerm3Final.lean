import ThomsonCertificate.N10StationarityLeftTerm3
import ThomsonNine.IntervalMul

namespace ThomsonTen

open ThomsonNine.Interval
open ThomsonNine.Interval.RatInterval

/-! The remaining left endpoint term is replayed with rational intervals.  The
    deliberately short decimal endpoints below are still much tighter than the
    final sign margin; all inequalities are discharged by `norm_num`. -/

def EL3_t4 : RatInterval := powNonneg EL_t2 (by
  norm_num [EL_t2, leftT, RatInterval.powNonneg]) 2
def EL3_s2t2 : RatInterval := mulNonneg EL3_sqrtTwo EL_t2
  (by norm_num [EL3_sqrtTwo])
  (by norm_num [EL_t2, leftT, RatInterval.powNonneg])
def EL3_radA : RatInterval := add (add EL3_t4 EL3_s2t2) (const 1)
def EL3_radB : RatInterval := add (sub EL3_t4 EL3_s2t2) (const 1)

def EL3_sqrtA : RatInterval :=
  ⟨(1318536928069113349 / 1000000000000000000 : ℚ),
   (1318536928069113350 / 1000000000000000000 : ℚ), by norm_num⟩
def EL3_sqrtB : RatInterval :=
  ⟨(768629753754736911 / 1000000000000000000 : ℚ),
   (768629753754736912 / 1000000000000000000 : ℚ), by norm_num⟩

theorem EL3_t4_mem : EL3_t4.mem
    ((63701661910807 / 100000000000000 : ℝ)^4) := by
  have h := mem_powNonneg (I := EL_t2)
      (by norm_num [EL_t2, leftT, RatInterval.powNonneg]) 2 EL_t2_mem
  convert h using 1 <;> norm_num [EL3_t4, EL_t2, leftT,
    RatInterval.powNonneg] <;> ring

theorem EL3_s2t2_mem : EL3_s2t2.mem
    (Real.sqrt 2 * (63701661910807 / 100000000000000 : ℝ)^2) :=
  mem_mulNonneg (by norm_num [EL3_sqrtTwo])
    (by norm_num [EL_t2, leftT, RatInterval.powNonneg])
    EL3_sqrtTwo_mem EL_t2_mem

theorem EL3_radA_mem : EL3_radA.mem
    ((63701661910807 / 100000000000000 : ℝ)^4 +
      Real.sqrt 2 * (63701661910807 / 100000000000000 : ℝ)^2 + 1) := by
  simpa [EL3_radA] using mem_add
    (mem_add EL3_t4_mem EL3_s2t2_mem) (mem_const 1)

theorem EL3_radB_mem : EL3_radB.mem
    ((63701661910807 / 100000000000000 : ℝ)^4 -
      Real.sqrt 2 * (63701661910807 / 100000000000000 : ℝ)^2 + 1) := by
  simpa [EL3_radB] using mem_add
    (mem_sub EL3_t4_mem EL3_s2t2_mem) (mem_const 1)

theorem EL3_sqrtA_mem : EL3_sqrtA.mem
    (Real.sqrt ((63701661910807 / 100000000000000 : ℝ)^4 +
      Real.sqrt 2 * (63701661910807 / 100000000000000 : ℝ)^2 + 1)) := by
  have h := mem_sqrtI (I := EL3_radA)
    (x := (63701661910807 / 100000000000000 : ℝ)^4 +
      Real.sqrt 2 * (63701661910807 / 100000000000000 : ℝ)^2 + 1)
    (lo := EL3_sqrtA.lo) (hi := EL3_sqrtA.hi)
    (by norm_num [EL3_sqrtA])
    (by norm_num [EL3_sqrtA, EL3_radA, EL3_radA, EL3_t4, EL3_s2t2,
      EL_t2, EL3_sqrtTwo, leftT, RatInterval.powNonneg,
      RatInterval.mulNonneg, RatInterval.add, RatInterval.sub,
      RatInterval.neg, RatInterval.const])
    (by norm_num [EL3_sqrtA])
    (by norm_num [EL3_sqrtA, EL3_radA, EL3_radA, EL3_t4, EL3_s2t2,
      EL_t2, EL3_sqrtTwo, leftT, RatInterval.powNonneg,
      RatInterval.mulNonneg, RatInterval.add, RatInterval.sub,
      RatInterval.neg, RatInterval.const])
    (by norm_num [EL3_sqrtA]) EL3_radA_mem (by positivity)
  simpa [sqrtI, EL3_sqrtA] using h

theorem EL3_sqrtB_mem : EL3_sqrtB.mem
    (Real.sqrt ((63701661910807 / 100000000000000 : ℝ)^4 -
      Real.sqrt 2 * (63701661910807 / 100000000000000 : ℝ)^2 + 1)) := by
  have h := mem_sqrtI (I := EL3_radB)
    (x := (63701661910807 / 100000000000000 : ℝ)^4 -
      Real.sqrt 2 * (63701661910807 / 100000000000000 : ℝ)^2 + 1)
    (lo := EL3_sqrtB.lo) (hi := EL3_sqrtB.hi)
    (by norm_num [EL3_sqrtB])
    (by norm_num [EL3_sqrtB, EL3_radB, EL3_t4, EL3_s2t2,
      EL_t2, EL3_sqrtTwo, leftT, RatInterval.powNonneg,
      RatInterval.mulNonneg, RatInterval.add, RatInterval.sub,
      RatInterval.neg, RatInterval.const])
    (by norm_num [EL3_sqrtB])
    (by norm_num [EL3_sqrtB, EL3_radB, EL3_t4, EL3_s2t2,
      EL_t2, EL3_sqrtTwo, leftT, RatInterval.powNonneg,
      RatInterval.mulNonneg, RatInterval.add, RatInterval.sub,
      RatInterval.neg, RatInterval.const])
    (by norm_num [EL3_sqrtB]) EL3_radB_mem (by
      have hs : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
      have hs2 : Real.sqrt (2 : ℝ) ≤ 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [sq_nonneg ((63701661910807 / 100000000000000 : ℝ)^2)])
  simpa [sqrtI, EL3_sqrtB] using h

def EL3_invA : RatInterval := invI EL3_sqrtA (by norm_num [EL3_sqrtA])
def EL3_invB : RatInterval := invI EL3_sqrtB (by norm_num [EL3_sqrtB])
def EL3_invA3 : RatInterval := powNonneg EL3_invA (by
  norm_num [EL3_invA, invI, EL3_sqrtA]) 3
def EL3_invB3 : RatInterval := powNonneg EL3_invB (by
  norm_num [EL3_invB, invI, EL3_sqrtB]) 3

noncomputable def EL3_xA : ℝ := Real.sqrt ((63701661910807 / 100000000000000 : ℝ)^4 +
  Real.sqrt 2 * (63701661910807 / 100000000000000 : ℝ)^2 + 1)
noncomputable def EL3_xB : ℝ := Real.sqrt ((63701661910807 / 100000000000000 : ℝ)^4 -
  Real.sqrt 2 * (63701661910807 / 100000000000000 : ℝ)^2 + 1)

theorem EL3_invA_mem : EL3_invA.mem
    (Real.sqrt ((63701661910807 / 100000000000000 : ℝ)^4 +
      Real.sqrt 2 * (63701661910807 / 100000000000000 : ℝ)^2 + 1))⁻¹ :=
  mem_invI (by norm_num [EL3_sqrtA]) EL3_sqrtA_mem
theorem EL3_invB_mem : EL3_invB.mem
    (Real.sqrt ((63701661910807 / 100000000000000 : ℝ)^4 -
      Real.sqrt 2 * (63701661910807 / 100000000000000 : ℝ)^2 + 1))⁻¹ :=
  mem_invI (by norm_num [EL3_sqrtB]) EL3_sqrtB_mem
theorem EL3_invA3_mem : EL3_invA3.mem
    ((EL3_xA⁻¹)^3) :=
  by simpa [EL3_xA, EL3_invA3] using
    (mem_powNonneg (by norm_num [EL3_invA, invI, EL3_sqrtA]) 3 EL3_invA_mem)
theorem EL3_invB3_mem : EL3_invB3.mem
    ((EL3_xB⁻¹)^3) :=
  by simpa [EL3_xB, EL3_invB3] using
    (mem_powNonneg (by norm_num [EL3_invB, invI, EL3_sqrtB]) 3 EL3_invB_mem)

def EL3_2t : RatInterval := scale 2 (by norm_num) leftT
def EL3_Afirst : RatInterval := mulNonneg EL3_2t EL3_invA
  (by norm_num [EL3_2t, RatInterval.scale, leftT])
  (by norm_num [EL3_invA, invI, EL3_sqrtA])
def EL3_Asecond : RatInterval := mulNonneg EL3_anum EL3_invA3
  (by norm_num [EL3_anum, EL3_pbase, EL3_abase, EL3_sqrtTwo, EL_t2,
    leftT, RatInterval.mulNonneg, RatInterval.add, RatInterval.scale,
    RatInterval.const, RatInterval.powNonneg])
  (by norm_num [EL3_invA3, EL3_invA, invI, EL3_sqrtA, RatInterval.powNonneg])
def EL3_Bfirst : RatInterval := mulNonneg EL3_2t EL3_invB
  (by norm_num [EL3_2t, RatInterval.scale, leftT])
  (by norm_num [EL3_invB, invI, EL3_sqrtB])
def EL3_Bsecond : RatInterval := mulMixed EL3_bnum EL3_invB3
  (by norm_num [EL3_invB3, EL3_invB, invI, EL3_sqrtB, RatInterval.powNonneg])
def EL3_partA : RatInterval := sub EL3_Afirst EL3_Asecond
def EL3_partB : RatInterval := sub EL3_Bfirst EL3_Bsecond
def EL3_term3 : RatInterval := scale 4 (by norm_num) (add EL3_partA EL3_partB)

theorem EL3_term3_mem : EL3_term3.mem (4 * (
    2 * (63701661910807 / 100000000000000 : ℝ) *
      (Real.sqrt ((63701661910807 / 100000000000000 : ℝ)^4 +
        Real.sqrt 2 * (63701661910807 / 100000000000000 : ℝ)^2 + 1))⁻¹ -
    (((1 + (63701661910807 / 100000000000000 : ℝ)^2) *
      (63701661910807 / 100000000000000 : ℝ)) *
      (2 * (63701661910807 / 100000000000000 : ℝ)^2 + Real.sqrt 2)) *
      ((Real.sqrt ((63701661910807 / 100000000000000 : ℝ)^4 +
        Real.sqrt 2 * (63701661910807 / 100000000000000 : ℝ)^2 + 1))⁻¹)^3 +
    2 * (63701661910807 / 100000000000000 : ℝ) *
      (Real.sqrt ((63701661910807 / 100000000000000 : ℝ)^4 -
        Real.sqrt 2 * (63701661910807 / 100000000000000 : ℝ)^2 + 1))⁻¹ -
    (((1 + (63701661910807 / 100000000000000 : ℝ)^2) *
      (63701661910807 / 100000000000000 : ℝ)) *
      (2 * (63701661910807 / 100000000000000 : ℝ)^2 - Real.sqrt 2)) *
      ((Real.sqrt ((63701661910807 / 100000000000000 : ℝ)^4 -
        Real.sqrt 2 * (63701661910807 / 100000000000000 : ℝ)^2 + 1))⁻¹)^3)) := by
  have hA1 := mem_mulNonneg
    (by norm_num [EL3_2t, RatInterval.scale, leftT])
    (by norm_num [EL3_invA, invI, EL3_sqrtA])
    (mem_scale (c := 2) (by norm_num) leftT_mem) EL3_invA_mem
  have hA2 := mem_mulNonneg
    (by norm_num [EL3_anum, EL3_pbase, EL3_abase, EL3_sqrtTwo, EL_t2,
      leftT, RatInterval.mulNonneg, RatInterval.add, RatInterval.scale,
      RatInterval.const, RatInterval.powNonneg])
    (by norm_num [EL3_invA3, EL3_invA, invI, EL3_sqrtA, RatInterval.powNonneg])
    EL3_anum_mem EL3_invA3_mem
  have hB1 := mem_mulNonneg
    (by norm_num [EL3_2t, RatInterval.scale, leftT])
    (by norm_num [EL3_invB, invI, EL3_sqrtB])
    (mem_scale (c := 2) (by norm_num) leftT_mem) EL3_invB_mem
  have hB2 := mem_mulMixed
    (by norm_num [EL3_invB3, EL3_invB, invI, EL3_sqrtB, RatInterval.powNonneg])
    EL3_bnum_mem EL3_invB3_mem
  have hsum := mem_add (mem_sub hA1 hA2) (mem_sub hB1 hB2)
  have hscale := mem_scale (c := 4) (by norm_num) hsum
  convert hscale using 1 <;>
    norm_num [EL3_term3, EL3_partA, EL3_partB, EL3_Afirst,
      EL3_Asecond, EL3_Bfirst, EL3_Bsecond, EL3_2t, EL3_invA3,
      EL3_invB3, EL3_invA, EL3_invB, invI, EL3_sqrtA, EL3_sqrtB,
      EL3_anum, EL3_bnum, EL3_pbase, EL3_abase, EL3_bbase,
      EL3_sqrtTwo, EL3_t4, EL3_s2t2, EL3_radA, EL3_radB, EL_t2,
      EL3_xA, EL3_xB,
      leftT, RatInterval.powNonneg, RatInterval.mulNonneg,
      RatInterval.mulMixed, RatInterval.scale, RatInterval.add,
      RatInterval.sub, RatInterval.neg, RatInterval.const] <;> ring

def EL3_stationarity : RatInterval := add (add EL_term1 EL2_term2) EL3_term3

theorem d4dStationarity_left_endpoint_negative :
    4 * (((63701661910807 / 100000000000000 : ℝ) + 1) /
      Real.sqrt (1 + (63701661910807 / 100000000000000 : ℝ)^2) -
      Real.sqrt (1 + (63701661910807 / 100000000000000 : ℝ)^2) /
        (63701661910807 / 100000000000000 : ℝ)^2) +
      (1 - ((63701661910807 / 100000000000000 : ℝ)^2)⁻¹) *
        (1 + 2 * Real.sqrt 2) +
      4 * (2 * (63701661910807 / 100000000000000 : ℝ) *
        (Real.sqrt ((63701661910807 / 100000000000000 : ℝ)^4 +
          Real.sqrt 2 * (63701661910807 / 100000000000000 : ℝ)^2 + 1))⁻¹ -
      (((1 + (63701661910807 / 100000000000000 : ℝ)^2) *
        (63701661910807 / 100000000000000 : ℝ)) *
        (2 * (63701661910807 / 100000000000000 : ℝ)^2 + Real.sqrt 2)) *
        ((Real.sqrt ((63701661910807 / 100000000000000 : ℝ)^4 +
          Real.sqrt 2 * (63701661910807 / 100000000000000 : ℝ)^2 + 1))⁻¹)^3 +
      2 * (63701661910807 / 100000000000000 : ℝ) *
        (Real.sqrt ((63701661910807 / 100000000000000 : ℝ)^4 -
          Real.sqrt 2 * (63701661910807 / 100000000000000 : ℝ)^2 + 1))⁻¹ -
      (((1 + (63701661910807 / 100000000000000 : ℝ)^2) *
        (63701661910807 / 100000000000000 : ℝ)) *
        (2 * (63701661910807 / 100000000000000 : ℝ)^2 - Real.sqrt 2)) *
        ((Real.sqrt ((63701661910807 / 100000000000000 : ℝ)^4 -
          Real.sqrt 2 * (63701661910807 / 100000000000000 : ℝ)^2 + 1))⁻¹)^3) < 0 := by
  have hm := EL3_term3_mem
  have hsum := RatInterval.mem_add (RatInterval.mem_add EL_term1_mem EL2_term2_mem) hm
  exact lt_of_le_of_lt hsum.2 (by
    norm_num [EL3_stationarity, EL3_term3, EL3_partA, EL3_partB,
      EL3_Afirst, EL3_Asecond, EL3_Bfirst, EL3_Bsecond, EL3_2t,
      EL3_invA3, EL3_invB3, EL3_invA, EL3_invB, invI, EL3_sqrtA,
      EL3_sqrtB, EL3_anum, EL3_bnum, EL3_pbase, EL3_abase, EL3_bbase,
      EL3_sqrtTwo, EL3_t4, EL3_s2t2, EL3_radA, EL3_radB, EL_t2,
      EL_term1, EL_p1, EL_p2, EL_tPlus, EL_invT2, EL_invC, EL_sqrtC,
      EL2_term2, EL2_m1, EL2_p3, leftT, sqrtTwoI,
      RatInterval.powNonneg, RatInterval.mulNonneg, RatInterval.mulMixed,
      RatInterval.scale, RatInterval.add, RatInterval.sub,
      RatInterval.neg, RatInterval.const])

end ThomsonTen
