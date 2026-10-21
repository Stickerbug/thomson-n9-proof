import ThomsonNine.LocalSparseHessianAAABase

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace ThomsonNine.LocalSparseHessianAAA

open ThomsonNine.Interval ThomsonNine.Interval.SparsePolynomial
open ThomsonNine.Interval.RatInterval

private def termBound_000 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_000 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_000.mem (hessianTerm c x .t000) := by
  have hzero : hessianTerm c x .t000 = 0 := by
    unfold hessianTerm
    rw [show exponents .t000 = ![0, 0, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_000, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_001 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_001 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_001.mem (hessianTerm c x .t001) := by
  have hzero : hessianTerm c x .t001 = 0 := by
    unfold hessianTerm
    rw [show exponents .t001 = ![0, 0, 1] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_001, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_002 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_002 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_002.mem (hessianTerm c x .t002) := by
  have hzero : hessianTerm c x .t002 = 0 := by
    unfold hessianTerm
    rw [show exponents .t002 = ![0, 0, 2] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_002, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_003 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_003 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_003.mem (hessianTerm c x .t003) := by
  have hzero : hessianTerm c x .t003 = 0 := by
    unfold hessianTerm
    rw [show exponents .t003 = ![0, 0, 3] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_003, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_004 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_004 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_004.mem (hessianTerm c x .t004) := by
  have hzero : hessianTerm c x .t004 = 0 := by
    unfold hessianTerm
    rw [show exponents .t004 = ![0, 0, 4] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_004, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_005 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_005 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_005.mem (hessianTerm c x .t005) := by
  have hzero : hessianTerm c x .t005 = 0 := by
    unfold hessianTerm
    rw [show exponents .t005 = ![0, 0, 5] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_005, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_006 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_006 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_006.mem (hessianTerm c x .t006) := by
  have hzero : hessianTerm c x .t006 = 0 := by
    unfold hessianTerm
    rw [show exponents .t006 = ![0, 0, 6] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_006, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_007 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_007 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_007.mem (hessianTerm c x .t007) := by
  have hzero : hessianTerm c x .t007 = 0 := by
    unfold hessianTerm
    rw [show exponents .t007 = ![0, 0, 7] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_007, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_008 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_008 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_008.mem (hessianTerm c x .t008) := by
  have hzero : hessianTerm c x .t008 = 0 := by
    unfold hessianTerm
    rw [show exponents .t008 = ![0, 0, 8] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_008, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_009 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_009 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_009.mem (hessianTerm c x .t009) := by
  have hzero : hessianTerm c x .t009 = 0 := by
    unfold hessianTerm
    rw [show exponents .t009 = ![0, 0, 9] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_009, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_010 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_010 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_010.mem (hessianTerm c x .t010) := by
  have hzero : hessianTerm c x .t010 = 0 := by
    unfold hessianTerm
    rw [show exponents .t010 = ![0, 0, 10] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_010, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_011 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_011 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_011.mem (hessianTerm c x .t011) := by
  have hzero : hessianTerm c x .t011 = 0 := by
    unfold hessianTerm
    rw [show exponents .t011 = ![0, 0, 11] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_011, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_012 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_012 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_012.mem (hessianTerm c x .t012) := by
  have hzero : hessianTerm c x .t012 = 0 := by
    unfold hessianTerm
    rw [show exponents .t012 = ![0, 0, 12] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_012, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_013 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_013 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_013.mem (hessianTerm c x .t013) := by
  have hzero : hessianTerm c x .t013 = 0 := by
    unfold hessianTerm
    rw [show exponents .t013 = ![0, 0, 13] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_013, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_014 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_014 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_014.mem (hessianTerm c x .t014) := by
  have hzero : hessianTerm c x .t014 = 0 := by
    unfold hessianTerm
    rw [show exponents .t014 = ![0, 0, 14] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_014, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_015 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_015 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_015.mem (hessianTerm c x .t015) := by
  have hzero : hessianTerm c x .t015 = 0 := by
    unfold hessianTerm
    rw [show exponents .t015 = ![0, 0, 15] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_015, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_016 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_016 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_016.mem (hessianTerm c x .t016) := by
  have hzero : hessianTerm c x .t016 = 0 := by
    unfold hessianTerm
    rw [show exponents .t016 = ![0, 0, 16] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_016, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_017 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_017 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_017.mem (hessianTerm c x .t017) := by
  have hzero : hessianTerm c x .t017 = 0 := by
    unfold hessianTerm
    rw [show exponents .t017 = ![0, 0, 17] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_017, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_018 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_018 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_018.mem (hessianTerm c x .t018) := by
  have hzero : hessianTerm c x .t018 = 0 := by
    unfold hessianTerm
    rw [show exponents .t018 = ![0, 0, 18] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_018, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_019 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_019 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_019.mem (hessianTerm c x .t019) := by
  have hzero : hessianTerm c x .t019 = 0 := by
    unfold hessianTerm
    rw [show exponents .t019 = ![0, 0, 19] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_019, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_020 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_020 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_020.mem (hessianTerm c x .t020) := by
  have hzero : hessianTerm c x .t020 = 0 := by
    unfold hessianTerm
    rw [show exponents .t020 = ![0, 0, 20] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_020, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_021 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_021 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_021.mem (hessianTerm c x .t021) := by
  have hzero : hessianTerm c x .t021 = 0 := by
    unfold hessianTerm
    rw [show exponents .t021 = ![0, 0, 21] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_021, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_022 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_022 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_022.mem (hessianTerm c x .t022) := by
  have hzero : hessianTerm c x .t022 = 0 := by
    unfold hessianTerm
    rw [show exponents .t022 = ![0, 0, 22] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_022, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_023 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_023 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_023.mem (hessianTerm c x .t023) := by
  have hzero : hessianTerm c x .t023 = 0 := by
    unfold hessianTerm
    rw [show exponents .t023 = ![0, 0, 23] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_023, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_024 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_024 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_024.mem (hessianTerm c x .t024) := by
  have hzero : hessianTerm c x .t024 = 0 := by
    unfold hessianTerm
    rw [show exponents .t024 = ![0, 0, 24] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_024, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_025 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_025 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_025.mem (hessianTerm c x .t025) := by
  have hzero : hessianTerm c x .t025 = 0 := by
    unfold hessianTerm
    rw [show exponents .t025 = ![0, 0, 25] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_025, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_026 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_026 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_026.mem (hessianTerm c x .t026) := by
  have hzero : hessianTerm c x .t026 = 0 := by
    unfold hessianTerm
    rw [show exponents .t026 = ![0, 0, 26] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_026, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_027 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_027 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_027.mem (hessianTerm c x .t027) := by
  have hzero : hessianTerm c x .t027 = 0 := by
    unfold hessianTerm
    rw [show exponents .t027 = ![0, 0, 27] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_027, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_028 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_028 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_028.mem (hessianTerm c x .t028) := by
  have hzero : hessianTerm c x .t028 = 0 := by
    unfold hessianTerm
    rw [show exponents .t028 = ![0, 1, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_028, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_029 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_029 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_029.mem (hessianTerm c x .t029) := by
  have hzero : hessianTerm c x .t029 = 0 := by
    unfold hessianTerm
    rw [show exponents .t029 = ![0, 1, 1] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_029, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_030 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_030 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_030.mem (hessianTerm c x .t030) := by
  have hzero : hessianTerm c x .t030 = 0 := by
    unfold hessianTerm
    rw [show exponents .t030 = ![0, 1, 2] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_030, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_031 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_031 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_031.mem (hessianTerm c x .t031) := by
  have hzero : hessianTerm c x .t031 = 0 := by
    unfold hessianTerm
    rw [show exponents .t031 = ![0, 1, 3] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_031, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_032 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_032 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_032.mem (hessianTerm c x .t032) := by
  have hzero : hessianTerm c x .t032 = 0 := by
    unfold hessianTerm
    rw [show exponents .t032 = ![0, 1, 4] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_032, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_033 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_033 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_033.mem (hessianTerm c x .t033) := by
  have hzero : hessianTerm c x .t033 = 0 := by
    unfold hessianTerm
    rw [show exponents .t033 = ![0, 1, 5] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_033, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_034 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_034 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_034.mem (hessianTerm c x .t034) := by
  have hzero : hessianTerm c x .t034 = 0 := by
    unfold hessianTerm
    rw [show exponents .t034 = ![0, 1, 6] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_034, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_035 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_035 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_035.mem (hessianTerm c x .t035) := by
  have hzero : hessianTerm c x .t035 = 0 := by
    unfold hessianTerm
    rw [show exponents .t035 = ![0, 1, 7] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_035, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_036 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_036 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_036.mem (hessianTerm c x .t036) := by
  have hzero : hessianTerm c x .t036 = 0 := by
    unfold hessianTerm
    rw [show exponents .t036 = ![0, 1, 8] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_036, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_037 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_037 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_037.mem (hessianTerm c x .t037) := by
  have hzero : hessianTerm c x .t037 = 0 := by
    unfold hessianTerm
    rw [show exponents .t037 = ![0, 1, 9] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_037, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_038 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_038 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_038.mem (hessianTerm c x .t038) := by
  have hzero : hessianTerm c x .t038 = 0 := by
    unfold hessianTerm
    rw [show exponents .t038 = ![0, 1, 10] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_038, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_039 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_039 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_039.mem (hessianTerm c x .t039) := by
  have hzero : hessianTerm c x .t039 = 0 := by
    unfold hessianTerm
    rw [show exponents .t039 = ![0, 2, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_039, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_040 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_040 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_040.mem (hessianTerm c x .t040) := by
  have hzero : hessianTerm c x .t040 = 0 := by
    unfold hessianTerm
    rw [show exponents .t040 = ![0, 2, 1] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_040, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_041 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_041 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_041.mem (hessianTerm c x .t041) := by
  have hzero : hessianTerm c x .t041 = 0 := by
    unfold hessianTerm
    rw [show exponents .t041 = ![0, 2, 2] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_041, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_042 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_042 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_042.mem (hessianTerm c x .t042) := by
  have hzero : hessianTerm c x .t042 = 0 := by
    unfold hessianTerm
    rw [show exponents .t042 = ![0, 2, 3] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_042, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_043 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_043 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_043.mem (hessianTerm c x .t043) := by
  have hzero : hessianTerm c x .t043 = 0 := by
    unfold hessianTerm
    rw [show exponents .t043 = ![0, 2, 4] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_043, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_044 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_044 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_044.mem (hessianTerm c x .t044) := by
  have hzero : hessianTerm c x .t044 = 0 := by
    unfold hessianTerm
    rw [show exponents .t044 = ![0, 2, 5] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_044, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_045 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_045 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_045.mem (hessianTerm c x .t045) := by
  have hzero : hessianTerm c x .t045 = 0 := by
    unfold hessianTerm
    rw [show exponents .t045 = ![0, 2, 6] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_045, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_046 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_046 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_046.mem (hessianTerm c x .t046) := by
  have hzero : hessianTerm c x .t046 = 0 := by
    unfold hessianTerm
    rw [show exponents .t046 = ![0, 2, 7] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_046, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_047 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_047 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_047.mem (hessianTerm c x .t047) := by
  have hzero : hessianTerm c x .t047 = 0 := by
    unfold hessianTerm
    rw [show exponents .t047 = ![0, 2, 8] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_047, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_048 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_048 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_048.mem (hessianTerm c x .t048) := by
  have hzero : hessianTerm c x .t048 = 0 := by
    unfold hessianTerm
    rw [show exponents .t048 = ![0, 2, 9] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_048, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_049 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_049 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_049.mem (hessianTerm c x .t049) := by
  have hzero : hessianTerm c x .t049 = 0 := by
    unfold hessianTerm
    rw [show exponents .t049 = ![0, 2, 10] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_049, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_050 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_050 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_050.mem (hessianTerm c x .t050) := by
  have hzero : hessianTerm c x .t050 = 0 := by
    unfold hessianTerm
    rw [show exponents .t050 = ![0, 3, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_050, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_051 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_051 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_051.mem (hessianTerm c x .t051) := by
  have hzero : hessianTerm c x .t051 = 0 := by
    unfold hessianTerm
    rw [show exponents .t051 = ![0, 3, 1] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_051, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_052 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_052 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_052.mem (hessianTerm c x .t052) := by
  have hzero : hessianTerm c x .t052 = 0 := by
    unfold hessianTerm
    rw [show exponents .t052 = ![0, 3, 2] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_052, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_053 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_053 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_053.mem (hessianTerm c x .t053) := by
  have hzero : hessianTerm c x .t053 = 0 := by
    unfold hessianTerm
    rw [show exponents .t053 = ![0, 3, 3] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_053, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_054 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_054 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_054.mem (hessianTerm c x .t054) := by
  have hzero : hessianTerm c x .t054 = 0 := by
    unfold hessianTerm
    rw [show exponents .t054 = ![0, 3, 4] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_054, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_055 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_055 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_055.mem (hessianTerm c x .t055) := by
  have hzero : hessianTerm c x .t055 = 0 := by
    unfold hessianTerm
    rw [show exponents .t055 = ![0, 3, 5] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_055, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_056 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_056 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_056.mem (hessianTerm c x .t056) := by
  have hzero : hessianTerm c x .t056 = 0 := by
    unfold hessianTerm
    rw [show exponents .t056 = ![0, 3, 6] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_056, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_057 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_057 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_057.mem (hessianTerm c x .t057) := by
  have hzero : hessianTerm c x .t057 = 0 := by
    unfold hessianTerm
    rw [show exponents .t057 = ![0, 3, 7] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_057, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_058 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_058 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_058.mem (hessianTerm c x .t058) := by
  have hzero : hessianTerm c x .t058 = 0 := by
    unfold hessianTerm
    rw [show exponents .t058 = ![0, 3, 8] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_058, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_059 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_059 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_059.mem (hessianTerm c x .t059) := by
  have hzero : hessianTerm c x .t059 = 0 := by
    unfold hessianTerm
    rw [show exponents .t059 = ![0, 3, 9] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_059, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_060 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_060 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_060.mem (hessianTerm c x .t060) := by
  have hzero : hessianTerm c x .t060 = 0 := by
    unfold hessianTerm
    rw [show exponents .t060 = ![0, 3, 10] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_060, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_061 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_061 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_061.mem (hessianTerm c x .t061) := by
  have hzero : hessianTerm c x .t061 = 0 := by
    unfold hessianTerm
    rw [show exponents .t061 = ![0, 4, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_061, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_062 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_062 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_062.mem (hessianTerm c x .t062) := by
  have hzero : hessianTerm c x .t062 = 0 := by
    unfold hessianTerm
    rw [show exponents .t062 = ![0, 4, 1] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_062, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_063 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_063 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_063.mem (hessianTerm c x .t063) := by
  have hzero : hessianTerm c x .t063 = 0 := by
    unfold hessianTerm
    rw [show exponents .t063 = ![0, 4, 2] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_063, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_064 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_064 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_064.mem (hessianTerm c x .t064) := by
  have hzero : hessianTerm c x .t064 = 0 := by
    unfold hessianTerm
    rw [show exponents .t064 = ![0, 4, 3] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_064, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_065 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_065 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_065.mem (hessianTerm c x .t065) := by
  have hzero : hessianTerm c x .t065 = 0 := by
    unfold hessianTerm
    rw [show exponents .t065 = ![0, 4, 4] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_065, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_066 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_066 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_066.mem (hessianTerm c x .t066) := by
  have hzero : hessianTerm c x .t066 = 0 := by
    unfold hessianTerm
    rw [show exponents .t066 = ![0, 4, 5] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_066, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_067 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_067 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_067.mem (hessianTerm c x .t067) := by
  have hzero : hessianTerm c x .t067 = 0 := by
    unfold hessianTerm
    rw [show exponents .t067 = ![0, 4, 6] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_067, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_068 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_068 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_068.mem (hessianTerm c x .t068) := by
  have hzero : hessianTerm c x .t068 = 0 := by
    unfold hessianTerm
    rw [show exponents .t068 = ![0, 4, 7] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_068, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_069 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_069 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_069.mem (hessianTerm c x .t069) := by
  have hzero : hessianTerm c x .t069 = 0 := by
    unfold hessianTerm
    rw [show exponents .t069 = ![0, 4, 8] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_069, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_070 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_070 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_070.mem (hessianTerm c x .t070) := by
  have hzero : hessianTerm c x .t070 = 0 := by
    unfold hessianTerm
    rw [show exponents .t070 = ![0, 4, 9] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_070, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_071 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_071 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_071.mem (hessianTerm c x .t071) := by
  have hzero : hessianTerm c x .t071 = 0 := by
    unfold hessianTerm
    rw [show exponents .t071 = ![0, 4, 10] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_071, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_072 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_072 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_072.mem (hessianTerm c x .t072) := by
  have hzero : hessianTerm c x .t072 = 0 := by
    unfold hessianTerm
    rw [show exponents .t072 = ![0, 5, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_072, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_073 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_073 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_073.mem (hessianTerm c x .t073) := by
  have hzero : hessianTerm c x .t073 = 0 := by
    unfold hessianTerm
    rw [show exponents .t073 = ![0, 5, 1] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_073, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_074 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_074 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_074.mem (hessianTerm c x .t074) := by
  have hzero : hessianTerm c x .t074 = 0 := by
    unfold hessianTerm
    rw [show exponents .t074 = ![0, 5, 2] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_074, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_075 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_075 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_075.mem (hessianTerm c x .t075) := by
  have hzero : hessianTerm c x .t075 = 0 := by
    unfold hessianTerm
    rw [show exponents .t075 = ![0, 5, 3] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_075, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_076 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_076 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_076.mem (hessianTerm c x .t076) := by
  have hzero : hessianTerm c x .t076 = 0 := by
    unfold hessianTerm
    rw [show exponents .t076 = ![0, 5, 4] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_076, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_077 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_077 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_077.mem (hessianTerm c x .t077) := by
  have hzero : hessianTerm c x .t077 = 0 := by
    unfold hessianTerm
    rw [show exponents .t077 = ![0, 5, 5] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_077, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_078 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_078 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_078.mem (hessianTerm c x .t078) := by
  have hzero : hessianTerm c x .t078 = 0 := by
    unfold hessianTerm
    rw [show exponents .t078 = ![0, 5, 6] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_078, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_079 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_079 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_079.mem (hessianTerm c x .t079) := by
  have hzero : hessianTerm c x .t079 = 0 := by
    unfold hessianTerm
    rw [show exponents .t079 = ![0, 5, 7] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_079, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_080 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_080 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_080.mem (hessianTerm c x .t080) := by
  have hzero : hessianTerm c x .t080 = 0 := by
    unfold hessianTerm
    rw [show exponents .t080 = ![0, 5, 8] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_080, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_081 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_081 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_081.mem (hessianTerm c x .t081) := by
  have hzero : hessianTerm c x .t081 = 0 := by
    unfold hessianTerm
    rw [show exponents .t081 = ![0, 5, 9] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_081, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_082 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_082 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_082.mem (hessianTerm c x .t082) := by
  have hzero : hessianTerm c x .t082 = 0 := by
    unfold hessianTerm
    rw [show exponents .t082 = ![0, 5, 10] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_082, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_083 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_083 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_083.mem (hessianTerm c x .t083) := by
  have hzero : hessianTerm c x .t083 = 0 := by
    unfold hessianTerm
    rw [show exponents .t083 = ![0, 6, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_083, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_084 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_084 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_084.mem (hessianTerm c x .t084) := by
  have hzero : hessianTerm c x .t084 = 0 := by
    unfold hessianTerm
    rw [show exponents .t084 = ![0, 6, 1] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_084, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_085 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_085 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_085.mem (hessianTerm c x .t085) := by
  have hzero : hessianTerm c x .t085 = 0 := by
    unfold hessianTerm
    rw [show exponents .t085 = ![0, 6, 2] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_085, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_086 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_086 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_086.mem (hessianTerm c x .t086) := by
  have hzero : hessianTerm c x .t086 = 0 := by
    unfold hessianTerm
    rw [show exponents .t086 = ![0, 6, 3] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_086, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_087 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_087 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_087.mem (hessianTerm c x .t087) := by
  have hzero : hessianTerm c x .t087 = 0 := by
    unfold hessianTerm
    rw [show exponents .t087 = ![0, 6, 4] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_087, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_088 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_088 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_088.mem (hessianTerm c x .t088) := by
  have hzero : hessianTerm c x .t088 = 0 := by
    unfold hessianTerm
    rw [show exponents .t088 = ![0, 6, 5] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_088, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_089 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_089 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_089.mem (hessianTerm c x .t089) := by
  have hzero : hessianTerm c x .t089 = 0 := by
    unfold hessianTerm
    rw [show exponents .t089 = ![0, 6, 6] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_089, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_090 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_090 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_090.mem (hessianTerm c x .t090) := by
  have hzero : hessianTerm c x .t090 = 0 := by
    unfold hessianTerm
    rw [show exponents .t090 = ![0, 6, 7] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_090, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_091 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_091 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_091.mem (hessianTerm c x .t091) := by
  have hzero : hessianTerm c x .t091 = 0 := by
    unfold hessianTerm
    rw [show exponents .t091 = ![0, 6, 8] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_091, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_092 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_092 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_092.mem (hessianTerm c x .t092) := by
  have hzero : hessianTerm c x .t092 = 0 := by
    unfold hessianTerm
    rw [show exponents .t092 = ![0, 6, 9] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_092, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_093 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_093 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_093.mem (hessianTerm c x .t093) := by
  have hzero : hessianTerm c x .t093 = 0 := by
    unfold hessianTerm
    rw [show exponents .t093 = ![0, 6, 10] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_093, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_094 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_094 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_094.mem (hessianTerm c x .t094) := by
  have hzero : hessianTerm c x .t094 = 0 := by
    unfold hessianTerm
    rw [show exponents .t094 = ![0, 7, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_094, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_095 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_095 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_095.mem (hessianTerm c x .t095) := by
  have hzero : hessianTerm c x .t095 = 0 := by
    unfold hessianTerm
    rw [show exponents .t095 = ![0, 7, 1] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_095, RatInterval.const] using mem_const (0 : ℚ)

def block_00 : List TermIndex := [.t000, .t001, .t002, .t003, .t004, .t005, .t006, .t007, .t008, .t009, .t010, .t011, .t012, .t013, .t014, .t015, .t016, .t017, .t018, .t019, .t020, .t021, .t022, .t023]
private def blockBound_00 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem block_mem_00 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    blockBound_00.mem (formalHessianEntry exponents c 0 0 x block_00) := by
  have h : (sumIntervals [termBound_000, termBound_001, termBound_002, termBound_003, termBound_004, termBound_005, termBound_006, termBound_007, termBound_008, termBound_009, termBound_010, termBound_011, termBound_012, termBound_013, termBound_014, termBound_015, termBound_016, termBound_017, termBound_018, termBound_019, termBound_020, termBound_021, termBound_022, termBound_023]).mem
      (formalHessianEntry exponents c 0 0 x block_00) := by
    exact (mem_add (term_mem_000 c x hC hP) (mem_add (term_mem_001 c x hC hP) (mem_add (term_mem_002 c x hC hP) (mem_add (term_mem_003 c x hC hP) (mem_add (term_mem_004 c x hC hP) (mem_add (term_mem_005 c x hC hP) (mem_add (term_mem_006 c x hC hP) (mem_add (term_mem_007 c x hC hP) (mem_add (term_mem_008 c x hC hP) (mem_add (term_mem_009 c x hC hP) (mem_add (term_mem_010 c x hC hP) (mem_add (term_mem_011 c x hC hP) (mem_add (term_mem_012 c x hC hP) (mem_add (term_mem_013 c x hC hP) (mem_add (term_mem_014 c x hC hP) (mem_add (term_mem_015 c x hC hP) (mem_add (term_mem_016 c x hC hP) (mem_add (term_mem_017 c x hC hP) (mem_add (term_mem_018 c x hC hP) (mem_add (term_mem_019 c x hC hP) (mem_add (term_mem_020 c x hC hP) (mem_add (term_mem_021 c x hC hP) (mem_add (term_mem_022 c x hC hP) (mem_add (term_mem_023 c x hC hP) (by simpa [sumIntervals, eval] using mem_const (0 : ℚ))))))))))))))))))))))))))
  exact mem_subset h
    (by norm_num [blockBound_00, sumIntervals, RatInterval.add, RatInterval.const, termBound_000, termBound_001, termBound_002, termBound_003, termBound_004, termBound_005, termBound_006, termBound_007, termBound_008, termBound_009, termBound_010, termBound_011, termBound_012, termBound_013, termBound_014, termBound_015, termBound_016, termBound_017, termBound_018, termBound_019, termBound_020, termBound_021, termBound_022, termBound_023])
    (by norm_num [blockBound_00, sumIntervals, RatInterval.add, RatInterval.const, termBound_000, termBound_001, termBound_002, termBound_003, termBound_004, termBound_005, termBound_006, termBound_007, termBound_008, termBound_009, termBound_010, termBound_011, termBound_012, termBound_013, termBound_014, termBound_015, termBound_016, termBound_017, termBound_018, termBound_019, termBound_020, termBound_021, termBound_022, termBound_023])

def block_01 : List TermIndex := [.t024, .t025, .t026, .t027, .t028, .t029, .t030, .t031, .t032, .t033, .t034, .t035, .t036, .t037, .t038, .t039, .t040, .t041, .t042, .t043, .t044, .t045, .t046, .t047]
private def blockBound_01 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem block_mem_01 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    blockBound_01.mem (formalHessianEntry exponents c 0 0 x block_01) := by
  have h : (sumIntervals [termBound_024, termBound_025, termBound_026, termBound_027, termBound_028, termBound_029, termBound_030, termBound_031, termBound_032, termBound_033, termBound_034, termBound_035, termBound_036, termBound_037, termBound_038, termBound_039, termBound_040, termBound_041, termBound_042, termBound_043, termBound_044, termBound_045, termBound_046, termBound_047]).mem
      (formalHessianEntry exponents c 0 0 x block_01) := by
    exact (mem_add (term_mem_024 c x hC hP) (mem_add (term_mem_025 c x hC hP) (mem_add (term_mem_026 c x hC hP) (mem_add (term_mem_027 c x hC hP) (mem_add (term_mem_028 c x hC hP) (mem_add (term_mem_029 c x hC hP) (mem_add (term_mem_030 c x hC hP) (mem_add (term_mem_031 c x hC hP) (mem_add (term_mem_032 c x hC hP) (mem_add (term_mem_033 c x hC hP) (mem_add (term_mem_034 c x hC hP) (mem_add (term_mem_035 c x hC hP) (mem_add (term_mem_036 c x hC hP) (mem_add (term_mem_037 c x hC hP) (mem_add (term_mem_038 c x hC hP) (mem_add (term_mem_039 c x hC hP) (mem_add (term_mem_040 c x hC hP) (mem_add (term_mem_041 c x hC hP) (mem_add (term_mem_042 c x hC hP) (mem_add (term_mem_043 c x hC hP) (mem_add (term_mem_044 c x hC hP) (mem_add (term_mem_045 c x hC hP) (mem_add (term_mem_046 c x hC hP) (mem_add (term_mem_047 c x hC hP) (by simpa [sumIntervals, eval] using mem_const (0 : ℚ))))))))))))))))))))))))))
  exact mem_subset h
    (by norm_num [blockBound_01, sumIntervals, RatInterval.add, RatInterval.const, termBound_024, termBound_025, termBound_026, termBound_027, termBound_028, termBound_029, termBound_030, termBound_031, termBound_032, termBound_033, termBound_034, termBound_035, termBound_036, termBound_037, termBound_038, termBound_039, termBound_040, termBound_041, termBound_042, termBound_043, termBound_044, termBound_045, termBound_046, termBound_047])
    (by norm_num [blockBound_01, sumIntervals, RatInterval.add, RatInterval.const, termBound_024, termBound_025, termBound_026, termBound_027, termBound_028, termBound_029, termBound_030, termBound_031, termBound_032, termBound_033, termBound_034, termBound_035, termBound_036, termBound_037, termBound_038, termBound_039, termBound_040, termBound_041, termBound_042, termBound_043, termBound_044, termBound_045, termBound_046, termBound_047])

def block_02 : List TermIndex := [.t048, .t049, .t050, .t051, .t052, .t053, .t054, .t055, .t056, .t057, .t058, .t059, .t060, .t061, .t062, .t063, .t064, .t065, .t066, .t067, .t068, .t069, .t070, .t071]
private def blockBound_02 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem block_mem_02 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    blockBound_02.mem (formalHessianEntry exponents c 0 0 x block_02) := by
  have h : (sumIntervals [termBound_048, termBound_049, termBound_050, termBound_051, termBound_052, termBound_053, termBound_054, termBound_055, termBound_056, termBound_057, termBound_058, termBound_059, termBound_060, termBound_061, termBound_062, termBound_063, termBound_064, termBound_065, termBound_066, termBound_067, termBound_068, termBound_069, termBound_070, termBound_071]).mem
      (formalHessianEntry exponents c 0 0 x block_02) := by
    exact (mem_add (term_mem_048 c x hC hP) (mem_add (term_mem_049 c x hC hP) (mem_add (term_mem_050 c x hC hP) (mem_add (term_mem_051 c x hC hP) (mem_add (term_mem_052 c x hC hP) (mem_add (term_mem_053 c x hC hP) (mem_add (term_mem_054 c x hC hP) (mem_add (term_mem_055 c x hC hP) (mem_add (term_mem_056 c x hC hP) (mem_add (term_mem_057 c x hC hP) (mem_add (term_mem_058 c x hC hP) (mem_add (term_mem_059 c x hC hP) (mem_add (term_mem_060 c x hC hP) (mem_add (term_mem_061 c x hC hP) (mem_add (term_mem_062 c x hC hP) (mem_add (term_mem_063 c x hC hP) (mem_add (term_mem_064 c x hC hP) (mem_add (term_mem_065 c x hC hP) (mem_add (term_mem_066 c x hC hP) (mem_add (term_mem_067 c x hC hP) (mem_add (term_mem_068 c x hC hP) (mem_add (term_mem_069 c x hC hP) (mem_add (term_mem_070 c x hC hP) (mem_add (term_mem_071 c x hC hP) (by simpa [sumIntervals, eval] using mem_const (0 : ℚ))))))))))))))))))))))))))
  exact mem_subset h
    (by norm_num [blockBound_02, sumIntervals, RatInterval.add, RatInterval.const, termBound_048, termBound_049, termBound_050, termBound_051, termBound_052, termBound_053, termBound_054, termBound_055, termBound_056, termBound_057, termBound_058, termBound_059, termBound_060, termBound_061, termBound_062, termBound_063, termBound_064, termBound_065, termBound_066, termBound_067, termBound_068, termBound_069, termBound_070, termBound_071])
    (by norm_num [blockBound_02, sumIntervals, RatInterval.add, RatInterval.const, termBound_048, termBound_049, termBound_050, termBound_051, termBound_052, termBound_053, termBound_054, termBound_055, termBound_056, termBound_057, termBound_058, termBound_059, termBound_060, termBound_061, termBound_062, termBound_063, termBound_064, termBound_065, termBound_066, termBound_067, termBound_068, termBound_069, termBound_070, termBound_071])

def block_03 : List TermIndex := [.t072, .t073, .t074, .t075, .t076, .t077, .t078, .t079, .t080, .t081, .t082, .t083, .t084, .t085, .t086, .t087, .t088, .t089, .t090, .t091, .t092, .t093, .t094, .t095]
private def blockBound_03 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem block_mem_03 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    blockBound_03.mem (formalHessianEntry exponents c 0 0 x block_03) := by
  have h : (sumIntervals [termBound_072, termBound_073, termBound_074, termBound_075, termBound_076, termBound_077, termBound_078, termBound_079, termBound_080, termBound_081, termBound_082, termBound_083, termBound_084, termBound_085, termBound_086, termBound_087, termBound_088, termBound_089, termBound_090, termBound_091, termBound_092, termBound_093, termBound_094, termBound_095]).mem
      (formalHessianEntry exponents c 0 0 x block_03) := by
    exact (mem_add (term_mem_072 c x hC hP) (mem_add (term_mem_073 c x hC hP) (mem_add (term_mem_074 c x hC hP) (mem_add (term_mem_075 c x hC hP) (mem_add (term_mem_076 c x hC hP) (mem_add (term_mem_077 c x hC hP) (mem_add (term_mem_078 c x hC hP) (mem_add (term_mem_079 c x hC hP) (mem_add (term_mem_080 c x hC hP) (mem_add (term_mem_081 c x hC hP) (mem_add (term_mem_082 c x hC hP) (mem_add (term_mem_083 c x hC hP) (mem_add (term_mem_084 c x hC hP) (mem_add (term_mem_085 c x hC hP) (mem_add (term_mem_086 c x hC hP) (mem_add (term_mem_087 c x hC hP) (mem_add (term_mem_088 c x hC hP) (mem_add (term_mem_089 c x hC hP) (mem_add (term_mem_090 c x hC hP) (mem_add (term_mem_091 c x hC hP) (mem_add (term_mem_092 c x hC hP) (mem_add (term_mem_093 c x hC hP) (mem_add (term_mem_094 c x hC hP) (mem_add (term_mem_095 c x hC hP) (by simpa [sumIntervals, eval] using mem_const (0 : ℚ))))))))))))))))))))))))))
  exact mem_subset h
    (by norm_num [blockBound_03, sumIntervals, RatInterval.add, RatInterval.const, termBound_072, termBound_073, termBound_074, termBound_075, termBound_076, termBound_077, termBound_078, termBound_079, termBound_080, termBound_081, termBound_082, termBound_083, termBound_084, termBound_085, termBound_086, termBound_087, termBound_088, termBound_089, termBound_090, termBound_091, termBound_092, termBound_093, termBound_094, termBound_095])
    (by norm_num [blockBound_03, sumIntervals, RatInterval.add, RatInterval.const, termBound_072, termBound_073, termBound_074, termBound_075, termBound_076, termBound_077, termBound_078, termBound_079, termBound_080, termBound_081, termBound_082, termBound_083, termBound_084, termBound_085, termBound_086, termBound_087, termBound_088, termBound_089, termBound_090, termBound_091, termBound_092, termBound_093, termBound_094, termBound_095])

def chunkTerms_00 : List TermIndex :=
  block_00 ++ (block_01 ++ (block_02 ++ (block_03 ++ ([]))))

def chunkInterval_00 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩

theorem chunk00_mem (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hx : ∀ j, (relativeBox j).mem (x j)) :
    chunkInterval_00.mem
      (formalHessianEntry exponents c 0 0 x chunkTerms_00) := by
  have hP := power_enclosures x hx
  have h : (sumIntervals [blockBound_00, blockBound_01, blockBound_02, blockBound_03]).mem
      (formalHessianEntry exponents c 0 0 x chunkTerms_00) := by
    simp only [chunkTerms_00, hessian_append, hessian_nil]
    exact (mem_add (block_mem_00 c x hC hP) (mem_add (block_mem_01 c x hC hP) (mem_add (block_mem_02 c x hC hP) (mem_add (block_mem_03 c x hC hP) (by simpa [sumIntervals, eval] using mem_const (0 : ℚ))))))
  exact mem_subset h
    (by norm_num [chunkInterval_00, sumIntervals, RatInterval.add, RatInterval.const, blockBound_00, blockBound_01, blockBound_02, blockBound_03])
    (by norm_num [chunkInterval_00, sumIntervals, RatInterval.add, RatInterval.const, blockBound_00, blockBound_01, blockBound_02, blockBound_03])

end ThomsonNine.LocalSparseHessianAAA
