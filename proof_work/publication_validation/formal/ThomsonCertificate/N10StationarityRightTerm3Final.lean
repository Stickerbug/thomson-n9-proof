import ThomsonCertificate.N10StationarityRightTerm2
import ThomsonNine.IntervalMul

namespace ThomsonTen

open ThomsonNine.Interval
open ThomsonNine.Interval.RatInterval

/-! The remaining left endpoint term is replayed with rational intervals.  The
    deliberately short decimal endpoints below are still much tighter than the
    final sign margin; all inequalities are discharged by `norm_num`. -/

def ER3_pbase : RatInterval :=
  mulNonneg (add (const 1) ER_t2) rightT
    (by norm_num [ER_t2, rightT, RatInterval.add, RatInterval.const,
      RatInterval.powNonneg])
    (by norm_num [rightT])
def ER3_abase : RatInterval :=
  add (scale 2 (by norm_num) ER_t2) sqrtTwoI
def ER3_bbase : RatInterval :=
  sub (scale 2 (by norm_num) ER_t2) sqrtTwoI
def ER3_anum : RatInterval :=
  mulNonneg ER3_pbase ER3_abase
    (by norm_num [ER3_pbase, RatInterval.mulNonneg, RatInterval.add,
      RatInterval.const, ER_t2, rightT, RatInterval.powNonneg])
    (by norm_num [ER3_abase, RatInterval.add, RatInterval.scale,
      RatInterval.const, ER_t2, rightT, RatInterval.powNonneg,
      sqrtTwoI])
def ER3_bnum : RatInterval :=
  mulMixed ER3_bbase ER3_pbase
    (by norm_num [ER3_pbase, RatInterval.mulNonneg, RatInterval.add,
      RatInterval.const, ER_t2, rightT, RatInterval.powNonneg])

theorem ER3_pbase_mem : ER3_pbase.mem
    ((1 + (7962707738851 / 12500000000000 : ℝ)^2) *
      (7962707738851 / 12500000000000 : ℝ)) := by
  exact mem_mulNonneg
    (by norm_num [ER_t2, rightT, RatInterval.add, RatInterval.const,
      RatInterval.powNonneg]) (by norm_num [rightT])
    (mem_add (by simpa using (mem_const 1)) ER_t2_mem) rightT_mem

theorem ER3_abase_mem : ER3_abase.mem
    (2 * (7962707738851 / 12500000000000 : ℝ)^2 + Real.sqrt 2) := by
  have h := mem_add (mem_scale (c := 2) (by norm_num) ER_t2_mem)
    sqrtTwoI_mem
  simpa [ER3_abase, RatInterval.add, RatInterval.scale] using h

theorem ER3_bbase_mem : ER3_bbase.mem
    (2 * (7962707738851 / 12500000000000 : ℝ)^2 - Real.sqrt 2) := by
  exact mem_sub (mem_scale (c := 2) (by norm_num) ER_t2_mem)
    sqrtTwoI_mem

theorem ER3_anum_mem : ER3_anum.mem
    (((1 + (7962707738851 / 12500000000000 : ℝ)^2) *
      (7962707738851 / 12500000000000 : ℝ)) *
      (2 * (7962707738851 / 12500000000000 : ℝ)^2 + Real.sqrt 2)) :=
  mem_mulNonneg
    (by norm_num [ER3_pbase, RatInterval.mulNonneg, RatInterval.add,
      RatInterval.const, ER_t2, rightT, RatInterval.powNonneg])
    (by norm_num [ER3_abase, RatInterval.add, RatInterval.scale,
      RatInterval.const, ER_t2, rightT, RatInterval.powNonneg,
      sqrtTwoI]) ER3_pbase_mem ER3_abase_mem

theorem ER3_bnum_mem : ER3_bnum.mem
    ((2 * (7962707738851 / 12500000000000 : ℝ)^2 - Real.sqrt 2) *
      ((1 + (7962707738851 / 12500000000000 : ℝ)^2) *
      (7962707738851 / 12500000000000 : ℝ))) :=
  mem_mulMixed
    (by norm_num [ER3_pbase, RatInterval.mulNonneg, RatInterval.add,
      RatInterval.const, ER_t2, rightT, RatInterval.powNonneg])
    ER3_bbase_mem ER3_pbase_mem


def ER3_t4 : RatInterval := powNonneg ER_t2 (by
  norm_num [ER_t2, rightT, RatInterval.powNonneg]) 2
def ER3_s2t2 : RatInterval := mulNonneg sqrtTwoI ER_t2
  (by norm_num [sqrtTwoI])
  (by norm_num [ER_t2, rightT, RatInterval.powNonneg])
def ER3_radA : RatInterval := add (add ER3_t4 ER3_s2t2) (const 1)
def ER3_radB : RatInterval := add (sub ER3_t4 ER3_s2t2) (const 1)

def ER3_sqrtA : RatInterval :=
  ⟨(1318536928069124102 / 1000000000000000000 : ℚ),
   (1318536928069124103 / 1000000000000000000 : ℚ), by norm_num⟩
def ER3_sqrtB : RatInterval :=
  ⟨(768629753754731916 / 1000000000000000000 : ℚ),
   (768629753754731917 / 1000000000000000000 : ℚ), by norm_num⟩

theorem ER3_t4_mem : ER3_t4.mem
    ((7962707738851 / 12500000000000 : ℝ)^4) := by
  have h := mem_powNonneg (I := ER_t2)
      (by norm_num [ER_t2, rightT, RatInterval.powNonneg]) 2 ER_t2_mem
  convert h using 1 <;> norm_num [ER3_t4, ER_t2, rightT,
    RatInterval.powNonneg] <;> ring

theorem ER3_s2t2_mem : ER3_s2t2.mem
    (Real.sqrt 2 * (7962707738851 / 12500000000000 : ℝ)^2) :=
  mem_mulNonneg (by norm_num [sqrtTwoI])
    (by norm_num [ER_t2, rightT, RatInterval.powNonneg])
    sqrtTwoI_mem ER_t2_mem

theorem ER3_radA_mem : ER3_radA.mem
    ((7962707738851 / 12500000000000 : ℝ)^4 +
      Real.sqrt 2 * (7962707738851 / 12500000000000 : ℝ)^2 + 1) := by
  simpa [ER3_radA] using mem_add
    (mem_add ER3_t4_mem ER3_s2t2_mem) (mem_const 1)

theorem ER3_radB_mem : ER3_radB.mem
    ((7962707738851 / 12500000000000 : ℝ)^4 -
      Real.sqrt 2 * (7962707738851 / 12500000000000 : ℝ)^2 + 1) := by
  simpa [ER3_radB] using mem_add
    (mem_sub ER3_t4_mem ER3_s2t2_mem) (mem_const 1)

theorem ER3_sqrtA_mem : ER3_sqrtA.mem
    (Real.sqrt ((7962707738851 / 12500000000000 : ℝ)^4 +
      Real.sqrt 2 * (7962707738851 / 12500000000000 : ℝ)^2 + 1)) := by
  have h := mem_sqrtI (I := ER3_radA)
    (x := (7962707738851 / 12500000000000 : ℝ)^4 +
      Real.sqrt 2 * (7962707738851 / 12500000000000 : ℝ)^2 + 1)
    (lo := ER3_sqrtA.lo) (hi := ER3_sqrtA.hi)
    (by norm_num [ER3_sqrtA])
    (by norm_num [ER3_sqrtA, ER3_radA, ER3_radA, ER3_t4, ER3_s2t2,
      ER_t2, sqrtTwoI, rightT, RatInterval.powNonneg,
      RatInterval.mulNonneg, RatInterval.add, RatInterval.sub,
      RatInterval.neg, RatInterval.const])
    (by norm_num [ER3_sqrtA])
    (by norm_num [ER3_sqrtA, ER3_radA, ER3_radA, ER3_t4, ER3_s2t2,
      ER_t2, sqrtTwoI, rightT, RatInterval.powNonneg,
      RatInterval.mulNonneg, RatInterval.add, RatInterval.sub,
      RatInterval.neg, RatInterval.const])
    (by norm_num [ER3_sqrtA]) ER3_radA_mem (by positivity)
  simpa [sqrtI, ER3_sqrtA] using h

theorem ER3_sqrtB_mem : ER3_sqrtB.mem
    (Real.sqrt ((7962707738851 / 12500000000000 : ℝ)^4 -
      Real.sqrt 2 * (7962707738851 / 12500000000000 : ℝ)^2 + 1)) := by
  have h := mem_sqrtI (I := ER3_radB)
    (x := (7962707738851 / 12500000000000 : ℝ)^4 -
      Real.sqrt 2 * (7962707738851 / 12500000000000 : ℝ)^2 + 1)
    (lo := ER3_sqrtB.lo) (hi := ER3_sqrtB.hi)
    (by norm_num [ER3_sqrtB])
    (by norm_num [ER3_sqrtB, ER3_radB, ER3_t4, ER3_s2t2,
      ER_t2, sqrtTwoI, rightT, RatInterval.powNonneg,
      RatInterval.mulNonneg, RatInterval.add, RatInterval.sub,
      RatInterval.neg, RatInterval.const])
    (by norm_num [ER3_sqrtB])
    (by norm_num [ER3_sqrtB, ER3_radB, ER3_t4, ER3_s2t2,
      ER_t2, sqrtTwoI, rightT, RatInterval.powNonneg,
      RatInterval.mulNonneg, RatInterval.add, RatInterval.sub,
      RatInterval.neg, RatInterval.const])
    (by norm_num [ER3_sqrtB]) ER3_radB_mem (by
      have hs : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
      have hs2 : Real.sqrt (2 : ℝ) ≤ 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [sq_nonneg ((7962707738851 / 12500000000000 : ℝ)^2)])
  simpa [sqrtI, ER3_sqrtB] using h

def ER3_invA : RatInterval := invI ER3_sqrtA (by norm_num [ER3_sqrtA])
def ER3_invB : RatInterval := invI ER3_sqrtB (by norm_num [ER3_sqrtB])
def ER3_invA3 : RatInterval := powNonneg ER3_invA (by
  norm_num [ER3_invA, invI, ER3_sqrtA]) 3
def ER3_invB3 : RatInterval := powNonneg ER3_invB (by
  norm_num [ER3_invB, invI, ER3_sqrtB]) 3

noncomputable def ER3_xA : ℝ := Real.sqrt ((7962707738851 / 12500000000000 : ℝ)^4 +
  Real.sqrt 2 * (7962707738851 / 12500000000000 : ℝ)^2 + 1)
noncomputable def ER3_xB : ℝ := Real.sqrt ((7962707738851 / 12500000000000 : ℝ)^4 -
  Real.sqrt 2 * (7962707738851 / 12500000000000 : ℝ)^2 + 1)

theorem ER3_invA_mem : ER3_invA.mem
    (Real.sqrt ((7962707738851 / 12500000000000 : ℝ)^4 +
      Real.sqrt 2 * (7962707738851 / 12500000000000 : ℝ)^2 + 1))⁻¹ :=
  mem_invI (by norm_num [ER3_sqrtA]) ER3_sqrtA_mem
theorem ER3_invB_mem : ER3_invB.mem
    (Real.sqrt ((7962707738851 / 12500000000000 : ℝ)^4 -
      Real.sqrt 2 * (7962707738851 / 12500000000000 : ℝ)^2 + 1))⁻¹ :=
  mem_invI (by norm_num [ER3_sqrtB]) ER3_sqrtB_mem
theorem ER3_invA3_mem : ER3_invA3.mem
    ((ER3_xA⁻¹)^3) :=
  by simpa [ER3_xA, ER3_invA3] using
    (mem_powNonneg (by norm_num [ER3_invA, invI, ER3_sqrtA]) 3 ER3_invA_mem)
theorem ER3_invB3_mem : ER3_invB3.mem
    ((ER3_xB⁻¹)^3) :=
  by simpa [ER3_xB, ER3_invB3] using
    (mem_powNonneg (by norm_num [ER3_invB, invI, ER3_sqrtB]) 3 ER3_invB_mem)

def ER3_2t : RatInterval := scale 2 (by norm_num) rightT
def ER3_Afirst : RatInterval := mulNonneg ER3_2t ER3_invA
  (by norm_num [ER3_2t, RatInterval.scale, rightT])
  (by norm_num [ER3_invA, invI, ER3_sqrtA])
def ER3_Asecond : RatInterval := mulNonneg ER3_anum ER3_invA3
  (by norm_num [ER3_anum, ER3_pbase, ER3_abase, sqrtTwoI, ER_t2,
    rightT, RatInterval.mulNonneg, RatInterval.add, RatInterval.scale,
    RatInterval.const, RatInterval.powNonneg])
  (by norm_num [ER3_invA3, ER3_invA, invI, ER3_sqrtA, RatInterval.powNonneg])
def ER3_Bfirst : RatInterval := mulNonneg ER3_2t ER3_invB
  (by norm_num [ER3_2t, RatInterval.scale, rightT])
  (by norm_num [ER3_invB, invI, ER3_sqrtB])
def ER3_Bsecond : RatInterval := mulMixed ER3_bnum ER3_invB3
  (by norm_num [ER3_invB3, ER3_invB, invI, ER3_sqrtB, RatInterval.powNonneg])
def ER3_partA : RatInterval := sub ER3_Afirst ER3_Asecond
def ER3_partB : RatInterval := sub ER3_Bfirst ER3_Bsecond
def ER3_term3 : RatInterval := scale 4 (by norm_num) (add ER3_partA ER3_partB)

theorem ER3_term3_mem : ER3_term3.mem (4 * (
    2 * (7962707738851 / 12500000000000 : ℝ) *
      (Real.sqrt ((7962707738851 / 12500000000000 : ℝ)^4 +
        Real.sqrt 2 * (7962707738851 / 12500000000000 : ℝ)^2 + 1))⁻¹ -
    (((1 + (7962707738851 / 12500000000000 : ℝ)^2) *
      (7962707738851 / 12500000000000 : ℝ)) *
      (2 * (7962707738851 / 12500000000000 : ℝ)^2 + Real.sqrt 2)) *
      ((Real.sqrt ((7962707738851 / 12500000000000 : ℝ)^4 +
        Real.sqrt 2 * (7962707738851 / 12500000000000 : ℝ)^2 + 1))⁻¹)^3 +
    2 * (7962707738851 / 12500000000000 : ℝ) *
      (Real.sqrt ((7962707738851 / 12500000000000 : ℝ)^4 -
        Real.sqrt 2 * (7962707738851 / 12500000000000 : ℝ)^2 + 1))⁻¹ -
    (((1 + (7962707738851 / 12500000000000 : ℝ)^2) *
      (7962707738851 / 12500000000000 : ℝ)) *
      (2 * (7962707738851 / 12500000000000 : ℝ)^2 - Real.sqrt 2)) *
      ((Real.sqrt ((7962707738851 / 12500000000000 : ℝ)^4 -
        Real.sqrt 2 * (7962707738851 / 12500000000000 : ℝ)^2 + 1))⁻¹)^3)) := by
  have hA1 := mem_mulNonneg
    (by norm_num [ER3_2t, RatInterval.scale, rightT])
    (by norm_num [ER3_invA, invI, ER3_sqrtA])
    (mem_scale (c := 2) (by norm_num) rightT_mem) ER3_invA_mem
  have hA2 := mem_mulNonneg
    (by norm_num [ER3_anum, ER3_pbase, ER3_abase, sqrtTwoI, ER_t2,
      rightT, RatInterval.mulNonneg, RatInterval.add, RatInterval.scale,
      RatInterval.const, RatInterval.powNonneg])
    (by norm_num [ER3_invA3, ER3_invA, invI, ER3_sqrtA, RatInterval.powNonneg])
    ER3_anum_mem ER3_invA3_mem
  have hB1 := mem_mulNonneg
    (by norm_num [ER3_2t, RatInterval.scale, rightT])
    (by norm_num [ER3_invB, invI, ER3_sqrtB])
    (mem_scale (c := 2) (by norm_num) rightT_mem) ER3_invB_mem
  have hB2 := mem_mulMixed
    (by norm_num [ER3_invB3, ER3_invB, invI, ER3_sqrtB, RatInterval.powNonneg])
    ER3_bnum_mem ER3_invB3_mem
  have hsum := mem_add (mem_sub hA1 hA2) (mem_sub hB1 hB2)
  have hscale := mem_scale (c := 4) (by norm_num) hsum
  convert hscale using 1 <;>
    norm_num [ER3_term3, ER3_partA, ER3_partB, ER3_Afirst,
      ER3_Asecond, ER3_Bfirst, ER3_Bsecond, ER3_2t, ER3_invA3,
      ER3_invB3, ER3_invA, ER3_invB, invI, ER3_sqrtA, ER3_sqrtB,
      ER3_anum, ER3_bnum, ER3_pbase, ER3_abase, ER3_bbase,
      sqrtTwoI, ER3_t4, ER3_s2t2, ER3_radA, ER3_radB, ER_t2,
      ER3_xA, ER3_xB,
      rightT, RatInterval.powNonneg, RatInterval.mulNonneg,
      RatInterval.mulMixed, RatInterval.scale, RatInterval.add,
      RatInterval.sub, RatInterval.neg, RatInterval.const] <;> ring

def ER3_stationarity : RatInterval := add (add ER_term1 ER2_term2) ER3_term3

theorem d4dStationarity_right_endpoint_positive :
    4 * (((7962707738851 / 12500000000000 : ℝ) + 1) /
      Real.sqrt (1 + (7962707738851 / 12500000000000 : ℝ)^2) -
      Real.sqrt (1 + (7962707738851 / 12500000000000 : ℝ)^2) /
        (7962707738851 / 12500000000000 : ℝ)^2) +
      (1 - ((7962707738851 / 12500000000000 : ℝ)^2)⁻¹) *
        (1 + 2 * Real.sqrt 2) +
      4 * (2 * (7962707738851 / 12500000000000 : ℝ) *
        (Real.sqrt ((7962707738851 / 12500000000000 : ℝ)^4 +
          Real.sqrt 2 * (7962707738851 / 12500000000000 : ℝ)^2 + 1))⁻¹ -
      (((1 + (7962707738851 / 12500000000000 : ℝ)^2) *
        (7962707738851 / 12500000000000 : ℝ)) *
        (2 * (7962707738851 / 12500000000000 : ℝ)^2 + Real.sqrt 2)) *
        ((Real.sqrt ((7962707738851 / 12500000000000 : ℝ)^4 +
          Real.sqrt 2 * (7962707738851 / 12500000000000 : ℝ)^2 + 1))⁻¹)^3 +
      2 * (7962707738851 / 12500000000000 : ℝ) *
        (Real.sqrt ((7962707738851 / 12500000000000 : ℝ)^4 -
          Real.sqrt 2 * (7962707738851 / 12500000000000 : ℝ)^2 + 1))⁻¹ -
      (((1 + (7962707738851 / 12500000000000 : ℝ)^2) *
        (7962707738851 / 12500000000000 : ℝ)) *
        (2 * (7962707738851 / 12500000000000 : ℝ)^2 - Real.sqrt 2)) *
        ((Real.sqrt ((7962707738851 / 12500000000000 : ℝ)^4 -
          Real.sqrt 2 * (7962707738851 / 12500000000000 : ℝ)^2 + 1))⁻¹)^3) > 0 := by
  have hm := ER3_term3_mem
  have hsum := RatInterval.mem_add (RatInterval.mem_add ER_term1_mem ER2_term2_mem) hm
  exact lt_of_lt_of_le (by
    norm_num [ER3_stationarity, ER3_term3, ER3_partA, ER3_partB,
      ER3_Afirst, ER3_Asecond, ER3_Bfirst, ER3_Bsecond, ER3_2t,
      ER3_invA3, ER3_invB3, ER3_invA, ER3_invB, invI, ER3_sqrtA,
      ER3_sqrtB, ER3_anum, ER3_bnum, ER3_pbase, ER3_abase, ER3_bbase,
      sqrtTwoI, ER3_t4, ER3_s2t2, ER3_radA, ER3_radB, ER_t2,
      ER_term1, ER_p1, ER_p2, ER_tPlus, ER_invT2, ER_invC, ER_sqrtC,
      ER2_term2, ER2_m1, ER2_p3, rightT, sqrtTwoI,
      RatInterval.powNonneg, RatInterval.mulNonneg, RatInterval.mulMixed,
      RatInterval.scale, RatInterval.add, RatInterval.sub,
      RatInterval.neg, RatInterval.const]) hsum.1

end ThomsonTen
