import ThomsonNine.LocalSparseHessianAAABase

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace ThomsonNine.LocalSparseHessianAAA

open ThomsonNine.Interval ThomsonNine.Interval.SparsePolynomial
open ThomsonNine.Interval.RatInterval

private def termBound_096 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_096 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_096.mem (hessianTerm c x .t096) := by
  have hzero : hessianTerm c x .t096 = 0 := by
    unfold hessianTerm
    rw [show exponents .t096 = ![0, 7, 2] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_096, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_097 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_097 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_097.mem (hessianTerm c x .t097) := by
  have hzero : hessianTerm c x .t097 = 0 := by
    unfold hessianTerm
    rw [show exponents .t097 = ![0, 7, 3] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_097, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_098 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_098 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_098.mem (hessianTerm c x .t098) := by
  have hzero : hessianTerm c x .t098 = 0 := by
    unfold hessianTerm
    rw [show exponents .t098 = ![0, 7, 4] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_098, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_099 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_099 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_099.mem (hessianTerm c x .t099) := by
  have hzero : hessianTerm c x .t099 = 0 := by
    unfold hessianTerm
    rw [show exponents .t099 = ![0, 7, 5] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_099, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_100 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_100 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_100.mem (hessianTerm c x .t100) := by
  have hzero : hessianTerm c x .t100 = 0 := by
    unfold hessianTerm
    rw [show exponents .t100 = ![0, 7, 6] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_100, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_101 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_101 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_101.mem (hessianTerm c x .t101) := by
  have hzero : hessianTerm c x .t101 = 0 := by
    unfold hessianTerm
    rw [show exponents .t101 = ![0, 7, 7] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_101, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_102 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_102 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_102.mem (hessianTerm c x .t102) := by
  have hzero : hessianTerm c x .t102 = 0 := by
    unfold hessianTerm
    rw [show exponents .t102 = ![0, 7, 8] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_102, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_103 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_103 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_103.mem (hessianTerm c x .t103) := by
  have hzero : hessianTerm c x .t103 = 0 := by
    unfold hessianTerm
    rw [show exponents .t103 = ![0, 7, 9] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_103, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_104 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_104 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_104.mem (hessianTerm c x .t104) := by
  have hzero : hessianTerm c x .t104 = 0 := by
    unfold hessianTerm
    rw [show exponents .t104 = ![0, 7, 10] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_104, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_105 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_105 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_105.mem (hessianTerm c x .t105) := by
  have hzero : hessianTerm c x .t105 = 0 := by
    unfold hessianTerm
    rw [show exponents .t105 = ![0, 8, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_105, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_106 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_106 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_106.mem (hessianTerm c x .t106) := by
  have hzero : hessianTerm c x .t106 = 0 := by
    unfold hessianTerm
    rw [show exponents .t106 = ![0, 8, 1] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_106, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_107 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_107 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_107.mem (hessianTerm c x .t107) := by
  have hzero : hessianTerm c x .t107 = 0 := by
    unfold hessianTerm
    rw [show exponents .t107 = ![0, 8, 2] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_107, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_108 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_108 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_108.mem (hessianTerm c x .t108) := by
  have hzero : hessianTerm c x .t108 = 0 := by
    unfold hessianTerm
    rw [show exponents .t108 = ![0, 8, 3] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_108, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_109 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_109 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_109.mem (hessianTerm c x .t109) := by
  have hzero : hessianTerm c x .t109 = 0 := by
    unfold hessianTerm
    rw [show exponents .t109 = ![0, 8, 4] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_109, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_110 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_110 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_110.mem (hessianTerm c x .t110) := by
  have hzero : hessianTerm c x .t110 = 0 := by
    unfold hessianTerm
    rw [show exponents .t110 = ![0, 8, 5] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_110, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_111 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_111 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_111.mem (hessianTerm c x .t111) := by
  have hzero : hessianTerm c x .t111 = 0 := by
    unfold hessianTerm
    rw [show exponents .t111 = ![0, 8, 6] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_111, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_112 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_112 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_112.mem (hessianTerm c x .t112) := by
  have hzero : hessianTerm c x .t112 = 0 := by
    unfold hessianTerm
    rw [show exponents .t112 = ![0, 8, 7] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_112, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_113 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_113 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_113.mem (hessianTerm c x .t113) := by
  have hzero : hessianTerm c x .t113 = 0 := by
    unfold hessianTerm
    rw [show exponents .t113 = ![0, 8, 8] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_113, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_114 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_114 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_114.mem (hessianTerm c x .t114) := by
  have hzero : hessianTerm c x .t114 = 0 := by
    unfold hessianTerm
    rw [show exponents .t114 = ![0, 8, 9] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_114, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_115 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_115 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_115.mem (hessianTerm c x .t115) := by
  have hzero : hessianTerm c x .t115 = 0 := by
    unfold hessianTerm
    rw [show exponents .t115 = ![0, 8, 10] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_115, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_116 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_116 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_116.mem (hessianTerm c x .t116) := by
  have hzero : hessianTerm c x .t116 = 0 := by
    unfold hessianTerm
    rw [show exponents .t116 = ![0, 9, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_116, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_117 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_117 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_117.mem (hessianTerm c x .t117) := by
  have hzero : hessianTerm c x .t117 = 0 := by
    unfold hessianTerm
    rw [show exponents .t117 = ![0, 9, 1] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_117, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_118 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_118 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_118.mem (hessianTerm c x .t118) := by
  have hzero : hessianTerm c x .t118 = 0 := by
    unfold hessianTerm
    rw [show exponents .t118 = ![0, 9, 2] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_118, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_119 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_119 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_119.mem (hessianTerm c x .t119) := by
  have hzero : hessianTerm c x .t119 = 0 := by
    unfold hessianTerm
    rw [show exponents .t119 = ![0, 9, 3] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_119, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_120 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_120 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_120.mem (hessianTerm c x .t120) := by
  have hzero : hessianTerm c x .t120 = 0 := by
    unfold hessianTerm
    rw [show exponents .t120 = ![0, 9, 4] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_120, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_121 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_121 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_121.mem (hessianTerm c x .t121) := by
  have hzero : hessianTerm c x .t121 = 0 := by
    unfold hessianTerm
    rw [show exponents .t121 = ![0, 9, 5] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_121, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_122 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_122 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_122.mem (hessianTerm c x .t122) := by
  have hzero : hessianTerm c x .t122 = 0 := by
    unfold hessianTerm
    rw [show exponents .t122 = ![0, 9, 6] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_122, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_123 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_123 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_123.mem (hessianTerm c x .t123) := by
  have hzero : hessianTerm c x .t123 = 0 := by
    unfold hessianTerm
    rw [show exponents .t123 = ![0, 9, 7] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_123, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_124 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_124 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_124.mem (hessianTerm c x .t124) := by
  have hzero : hessianTerm c x .t124 = 0 := by
    unfold hessianTerm
    rw [show exponents .t124 = ![0, 9, 8] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_124, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_125 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_125 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_125.mem (hessianTerm c x .t125) := by
  have hzero : hessianTerm c x .t125 = 0 := by
    unfold hessianTerm
    rw [show exponents .t125 = ![0, 9, 9] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_125, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_126 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_126 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_126.mem (hessianTerm c x .t126) := by
  have hzero : hessianTerm c x .t126 = 0 := by
    unfold hessianTerm
    rw [show exponents .t126 = ![0, 9, 10] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_126, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_127 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_127 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_127.mem (hessianTerm c x .t127) := by
  have hzero : hessianTerm c x .t127 = 0 := by
    unfold hessianTerm
    rw [show exponents .t127 = ![0, 10, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_127, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_128 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_128 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_128.mem (hessianTerm c x .t128) := by
  have hzero : hessianTerm c x .t128 = 0 := by
    unfold hessianTerm
    rw [show exponents .t128 = ![0, 10, 1] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_128, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_129 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_129 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_129.mem (hessianTerm c x .t129) := by
  have hzero : hessianTerm c x .t129 = 0 := by
    unfold hessianTerm
    rw [show exponents .t129 = ![0, 10, 2] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_129, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_130 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_130 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_130.mem (hessianTerm c x .t130) := by
  have hzero : hessianTerm c x .t130 = 0 := by
    unfold hessianTerm
    rw [show exponents .t130 = ![0, 10, 3] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_130, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_131 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_131 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_131.mem (hessianTerm c x .t131) := by
  have hzero : hessianTerm c x .t131 = 0 := by
    unfold hessianTerm
    rw [show exponents .t131 = ![0, 10, 4] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_131, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_132 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_132 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_132.mem (hessianTerm c x .t132) := by
  have hzero : hessianTerm c x .t132 = 0 := by
    unfold hessianTerm
    rw [show exponents .t132 = ![0, 10, 5] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_132, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_133 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_133 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_133.mem (hessianTerm c x .t133) := by
  have hzero : hessianTerm c x .t133 = 0 := by
    unfold hessianTerm
    rw [show exponents .t133 = ![0, 10, 6] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_133, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_134 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_134 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_134.mem (hessianTerm c x .t134) := by
  have hzero : hessianTerm c x .t134 = 0 := by
    unfold hessianTerm
    rw [show exponents .t134 = ![0, 10, 7] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_134, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_135 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_135 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_135.mem (hessianTerm c x .t135) := by
  have hzero : hessianTerm c x .t135 = 0 := by
    unfold hessianTerm
    rw [show exponents .t135 = ![0, 10, 8] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_135, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_136 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_136 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_136.mem (hessianTerm c x .t136) := by
  have hzero : hessianTerm c x .t136 = 0 := by
    unfold hessianTerm
    rw [show exponents .t136 = ![0, 10, 9] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_136, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_137 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_137 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_137.mem (hessianTerm c x .t137) := by
  have hzero : hessianTerm c x .t137 = 0 := by
    unfold hessianTerm
    rw [show exponents .t137 = ![0, 10, 10] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_137, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_138 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_138 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_138.mem (hessianTerm c x .t138) := by
  have hzero : hessianTerm c x .t138 = 0 := by
    unfold hessianTerm
    rw [show exponents .t138 = ![0, 11, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_138, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_139 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_139 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_139.mem (hessianTerm c x .t139) := by
  have hzero : hessianTerm c x .t139 = 0 := by
    unfold hessianTerm
    rw [show exponents .t139 = ![0, 12, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_139, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_140 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_140 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_140.mem (hessianTerm c x .t140) := by
  have hzero : hessianTerm c x .t140 = 0 := by
    unfold hessianTerm
    rw [show exponents .t140 = ![0, 13, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_140, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_141 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_141 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_141.mem (hessianTerm c x .t141) := by
  have hzero : hessianTerm c x .t141 = 0 := by
    unfold hessianTerm
    rw [show exponents .t141 = ![0, 14, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_141, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_142 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_142 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_142.mem (hessianTerm c x .t142) := by
  have hzero : hessianTerm c x .t142 = 0 := by
    unfold hessianTerm
    rw [show exponents .t142 = ![0, 15, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_142, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_143 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_143 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_143.mem (hessianTerm c x .t143) := by
  have hzero : hessianTerm c x .t143 = 0 := by
    unfold hessianTerm
    rw [show exponents .t143 = ![0, 16, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_143, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_144 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_144 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_144.mem (hessianTerm c x .t144) := by
  have hzero : hessianTerm c x .t144 = 0 := by
    unfold hessianTerm
    rw [show exponents .t144 = ![0, 17, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_144, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_145 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_145 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_145.mem (hessianTerm c x .t145) := by
  have hzero : hessianTerm c x .t145 = 0 := by
    unfold hessianTerm
    rw [show exponents .t145 = ![0, 18, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_145, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_146 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_146 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_146.mem (hessianTerm c x .t146) := by
  have hzero : hessianTerm c x .t146 = 0 := by
    unfold hessianTerm
    rw [show exponents .t146 = ![0, 19, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_146, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_147 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_147 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_147.mem (hessianTerm c x .t147) := by
  have hzero : hessianTerm c x .t147 = 0 := by
    unfold hessianTerm
    rw [show exponents .t147 = ![0, 20, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_147, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_148 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_148 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_148.mem (hessianTerm c x .t148) := by
  have hzero : hessianTerm c x .t148 = 0 := by
    unfold hessianTerm
    rw [show exponents .t148 = ![0, 21, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_148, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_149 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_149 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_149.mem (hessianTerm c x .t149) := by
  have hzero : hessianTerm c x .t149 = 0 := by
    unfold hessianTerm
    rw [show exponents .t149 = ![0, 22, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_149, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_150 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_150 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_150.mem (hessianTerm c x .t150) := by
  have hzero : hessianTerm c x .t150 = 0 := by
    unfold hessianTerm
    rw [show exponents .t150 = ![0, 23, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_150, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_151 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_151 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_151.mem (hessianTerm c x .t151) := by
  have hzero : hessianTerm c x .t151 = 0 := by
    unfold hessianTerm
    rw [show exponents .t151 = ![0, 24, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_151, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_152 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_152 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_152.mem (hessianTerm c x .t152) := by
  have hzero : hessianTerm c x .t152 = 0 := by
    unfold hessianTerm
    rw [show exponents .t152 = ![0, 25, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_152, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_153 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_153 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_153.mem (hessianTerm c x .t153) := by
  have hzero : hessianTerm c x .t153 = 0 := by
    unfold hessianTerm
    rw [show exponents .t153 = ![0, 26, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_153, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_154 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_154 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_154.mem (hessianTerm c x .t154) := by
  have hzero : hessianTerm c x .t154 = 0 := by
    unfold hessianTerm
    rw [show exponents .t154 = ![0, 27, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_154, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_155 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_155 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_155.mem (hessianTerm c x .t155) := by
  have hzero : hessianTerm c x .t155 = 0 := by
    unfold hessianTerm
    rw [show exponents .t155 = ![1, 0, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_155, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_156 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_156 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_156.mem (hessianTerm c x .t156) := by
  have hzero : hessianTerm c x .t156 = 0 := by
    unfold hessianTerm
    rw [show exponents .t156 = ![1, 0, 1] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_156, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_157 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_157 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_157.mem (hessianTerm c x .t157) := by
  have hzero : hessianTerm c x .t157 = 0 := by
    unfold hessianTerm
    rw [show exponents .t157 = ![1, 0, 2] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_157, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_158 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_158 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_158.mem (hessianTerm c x .t158) := by
  have hzero : hessianTerm c x .t158 = 0 := by
    unfold hessianTerm
    rw [show exponents .t158 = ![1, 0, 3] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_158, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_159 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_159 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_159.mem (hessianTerm c x .t159) := by
  have hzero : hessianTerm c x .t159 = 0 := by
    unfold hessianTerm
    rw [show exponents .t159 = ![1, 0, 4] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_159, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_160 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_160 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_160.mem (hessianTerm c x .t160) := by
  have hzero : hessianTerm c x .t160 = 0 := by
    unfold hessianTerm
    rw [show exponents .t160 = ![1, 0, 5] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_160, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_161 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_161 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_161.mem (hessianTerm c x .t161) := by
  have hzero : hessianTerm c x .t161 = 0 := by
    unfold hessianTerm
    rw [show exponents .t161 = ![1, 0, 6] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_161, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_162 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_162 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_162.mem (hessianTerm c x .t162) := by
  have hzero : hessianTerm c x .t162 = 0 := by
    unfold hessianTerm
    rw [show exponents .t162 = ![1, 0, 7] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_162, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_163 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_163 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_163.mem (hessianTerm c x .t163) := by
  have hzero : hessianTerm c x .t163 = 0 := by
    unfold hessianTerm
    rw [show exponents .t163 = ![1, 0, 8] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_163, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_164 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_164 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_164.mem (hessianTerm c x .t164) := by
  have hzero : hessianTerm c x .t164 = 0 := by
    unfold hessianTerm
    rw [show exponents .t164 = ![1, 0, 9] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_164, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_165 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_165 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_165.mem (hessianTerm c x .t165) := by
  have hzero : hessianTerm c x .t165 = 0 := by
    unfold hessianTerm
    rw [show exponents .t165 = ![1, 0, 10] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_165, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_166 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_166 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_166.mem (hessianTerm c x .t166) := by
  have hzero : hessianTerm c x .t166 = 0 := by
    unfold hessianTerm
    rw [show exponents .t166 = ![1, 1, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_166, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_167 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_167 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_167.mem (hessianTerm c x .t167) := by
  have hzero : hessianTerm c x .t167 = 0 := by
    unfold hessianTerm
    rw [show exponents .t167 = ![1, 1, 1] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_167, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_168 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_168 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_168.mem (hessianTerm c x .t168) := by
  have hzero : hessianTerm c x .t168 = 0 := by
    unfold hessianTerm
    rw [show exponents .t168 = ![1, 1, 2] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_168, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_169 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_169 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_169.mem (hessianTerm c x .t169) := by
  have hzero : hessianTerm c x .t169 = 0 := by
    unfold hessianTerm
    rw [show exponents .t169 = ![1, 1, 3] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_169, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_170 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_170 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_170.mem (hessianTerm c x .t170) := by
  have hzero : hessianTerm c x .t170 = 0 := by
    unfold hessianTerm
    rw [show exponents .t170 = ![1, 1, 4] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_170, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_171 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_171 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_171.mem (hessianTerm c x .t171) := by
  have hzero : hessianTerm c x .t171 = 0 := by
    unfold hessianTerm
    rw [show exponents .t171 = ![1, 1, 5] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_171, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_172 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_172 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_172.mem (hessianTerm c x .t172) := by
  have hzero : hessianTerm c x .t172 = 0 := by
    unfold hessianTerm
    rw [show exponents .t172 = ![1, 1, 6] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_172, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_173 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_173 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_173.mem (hessianTerm c x .t173) := by
  have hzero : hessianTerm c x .t173 = 0 := by
    unfold hessianTerm
    rw [show exponents .t173 = ![1, 1, 7] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_173, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_174 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_174 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_174.mem (hessianTerm c x .t174) := by
  have hzero : hessianTerm c x .t174 = 0 := by
    unfold hessianTerm
    rw [show exponents .t174 = ![1, 1, 8] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_174, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_175 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_175 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_175.mem (hessianTerm c x .t175) := by
  have hzero : hessianTerm c x .t175 = 0 := by
    unfold hessianTerm
    rw [show exponents .t175 = ![1, 1, 9] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_175, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_176 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_176 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_176.mem (hessianTerm c x .t176) := by
  have hzero : hessianTerm c x .t176 = 0 := by
    unfold hessianTerm
    rw [show exponents .t176 = ![1, 2, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_176, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_177 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_177 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_177.mem (hessianTerm c x .t177) := by
  have hzero : hessianTerm c x .t177 = 0 := by
    unfold hessianTerm
    rw [show exponents .t177 = ![1, 2, 1] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_177, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_178 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_178 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_178.mem (hessianTerm c x .t178) := by
  have hzero : hessianTerm c x .t178 = 0 := by
    unfold hessianTerm
    rw [show exponents .t178 = ![1, 2, 2] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_178, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_179 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_179 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_179.mem (hessianTerm c x .t179) := by
  have hzero : hessianTerm c x .t179 = 0 := by
    unfold hessianTerm
    rw [show exponents .t179 = ![1, 2, 3] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_179, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_180 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_180 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_180.mem (hessianTerm c x .t180) := by
  have hzero : hessianTerm c x .t180 = 0 := by
    unfold hessianTerm
    rw [show exponents .t180 = ![1, 2, 4] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_180, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_181 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_181 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_181.mem (hessianTerm c x .t181) := by
  have hzero : hessianTerm c x .t181 = 0 := by
    unfold hessianTerm
    rw [show exponents .t181 = ![1, 2, 5] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_181, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_182 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_182 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_182.mem (hessianTerm c x .t182) := by
  have hzero : hessianTerm c x .t182 = 0 := by
    unfold hessianTerm
    rw [show exponents .t182 = ![1, 2, 6] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_182, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_183 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_183 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_183.mem (hessianTerm c x .t183) := by
  have hzero : hessianTerm c x .t183 = 0 := by
    unfold hessianTerm
    rw [show exponents .t183 = ![1, 2, 7] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_183, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_184 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_184 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_184.mem (hessianTerm c x .t184) := by
  have hzero : hessianTerm c x .t184 = 0 := by
    unfold hessianTerm
    rw [show exponents .t184 = ![1, 2, 8] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_184, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_185 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_185 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_185.mem (hessianTerm c x .t185) := by
  have hzero : hessianTerm c x .t185 = 0 := by
    unfold hessianTerm
    rw [show exponents .t185 = ![1, 2, 9] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_185, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_186 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_186 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_186.mem (hessianTerm c x .t186) := by
  have hzero : hessianTerm c x .t186 = 0 := by
    unfold hessianTerm
    rw [show exponents .t186 = ![1, 3, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_186, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_187 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_187 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_187.mem (hessianTerm c x .t187) := by
  have hzero : hessianTerm c x .t187 = 0 := by
    unfold hessianTerm
    rw [show exponents .t187 = ![1, 3, 1] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_187, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_188 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_188 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_188.mem (hessianTerm c x .t188) := by
  have hzero : hessianTerm c x .t188 = 0 := by
    unfold hessianTerm
    rw [show exponents .t188 = ![1, 3, 2] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_188, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_189 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_189 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_189.mem (hessianTerm c x .t189) := by
  have hzero : hessianTerm c x .t189 = 0 := by
    unfold hessianTerm
    rw [show exponents .t189 = ![1, 3, 3] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_189, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_190 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_190 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_190.mem (hessianTerm c x .t190) := by
  have hzero : hessianTerm c x .t190 = 0 := by
    unfold hessianTerm
    rw [show exponents .t190 = ![1, 3, 4] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_190, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_191 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_191 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_191.mem (hessianTerm c x .t191) := by
  have hzero : hessianTerm c x .t191 = 0 := by
    unfold hessianTerm
    rw [show exponents .t191 = ![1, 3, 5] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_191, RatInterval.const] using mem_const (0 : ℚ)

def block_04 : List TermIndex := [.t096, .t097, .t098, .t099, .t100, .t101, .t102, .t103, .t104, .t105, .t106, .t107, .t108, .t109, .t110, .t111, .t112, .t113, .t114, .t115, .t116, .t117, .t118, .t119]
private def blockBound_04 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem block_mem_04 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    blockBound_04.mem (formalHessianEntry exponents c 0 0 x block_04) := by
  have h : (sumIntervals [termBound_096, termBound_097, termBound_098, termBound_099, termBound_100, termBound_101, termBound_102, termBound_103, termBound_104, termBound_105, termBound_106, termBound_107, termBound_108, termBound_109, termBound_110, termBound_111, termBound_112, termBound_113, termBound_114, termBound_115, termBound_116, termBound_117, termBound_118, termBound_119]).mem
      (formalHessianEntry exponents c 0 0 x block_04) := by
    exact (mem_add (term_mem_096 c x hC hP) (mem_add (term_mem_097 c x hC hP) (mem_add (term_mem_098 c x hC hP) (mem_add (term_mem_099 c x hC hP) (mem_add (term_mem_100 c x hC hP) (mem_add (term_mem_101 c x hC hP) (mem_add (term_mem_102 c x hC hP) (mem_add (term_mem_103 c x hC hP) (mem_add (term_mem_104 c x hC hP) (mem_add (term_mem_105 c x hC hP) (mem_add (term_mem_106 c x hC hP) (mem_add (term_mem_107 c x hC hP) (mem_add (term_mem_108 c x hC hP) (mem_add (term_mem_109 c x hC hP) (mem_add (term_mem_110 c x hC hP) (mem_add (term_mem_111 c x hC hP) (mem_add (term_mem_112 c x hC hP) (mem_add (term_mem_113 c x hC hP) (mem_add (term_mem_114 c x hC hP) (mem_add (term_mem_115 c x hC hP) (mem_add (term_mem_116 c x hC hP) (mem_add (term_mem_117 c x hC hP) (mem_add (term_mem_118 c x hC hP) (mem_add (term_mem_119 c x hC hP) (by simpa [sumIntervals, eval] using mem_const (0 : ℚ))))))))))))))))))))))))))
  exact mem_subset h
    (by norm_num [blockBound_04, sumIntervals, RatInterval.add, RatInterval.const, termBound_096, termBound_097, termBound_098, termBound_099, termBound_100, termBound_101, termBound_102, termBound_103, termBound_104, termBound_105, termBound_106, termBound_107, termBound_108, termBound_109, termBound_110, termBound_111, termBound_112, termBound_113, termBound_114, termBound_115, termBound_116, termBound_117, termBound_118, termBound_119])
    (by norm_num [blockBound_04, sumIntervals, RatInterval.add, RatInterval.const, termBound_096, termBound_097, termBound_098, termBound_099, termBound_100, termBound_101, termBound_102, termBound_103, termBound_104, termBound_105, termBound_106, termBound_107, termBound_108, termBound_109, termBound_110, termBound_111, termBound_112, termBound_113, termBound_114, termBound_115, termBound_116, termBound_117, termBound_118, termBound_119])

def block_05 : List TermIndex := [.t120, .t121, .t122, .t123, .t124, .t125, .t126, .t127, .t128, .t129, .t130, .t131, .t132, .t133, .t134, .t135, .t136, .t137, .t138, .t139, .t140, .t141, .t142, .t143]
private def blockBound_05 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem block_mem_05 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    blockBound_05.mem (formalHessianEntry exponents c 0 0 x block_05) := by
  have h : (sumIntervals [termBound_120, termBound_121, termBound_122, termBound_123, termBound_124, termBound_125, termBound_126, termBound_127, termBound_128, termBound_129, termBound_130, termBound_131, termBound_132, termBound_133, termBound_134, termBound_135, termBound_136, termBound_137, termBound_138, termBound_139, termBound_140, termBound_141, termBound_142, termBound_143]).mem
      (formalHessianEntry exponents c 0 0 x block_05) := by
    exact (mem_add (term_mem_120 c x hC hP) (mem_add (term_mem_121 c x hC hP) (mem_add (term_mem_122 c x hC hP) (mem_add (term_mem_123 c x hC hP) (mem_add (term_mem_124 c x hC hP) (mem_add (term_mem_125 c x hC hP) (mem_add (term_mem_126 c x hC hP) (mem_add (term_mem_127 c x hC hP) (mem_add (term_mem_128 c x hC hP) (mem_add (term_mem_129 c x hC hP) (mem_add (term_mem_130 c x hC hP) (mem_add (term_mem_131 c x hC hP) (mem_add (term_mem_132 c x hC hP) (mem_add (term_mem_133 c x hC hP) (mem_add (term_mem_134 c x hC hP) (mem_add (term_mem_135 c x hC hP) (mem_add (term_mem_136 c x hC hP) (mem_add (term_mem_137 c x hC hP) (mem_add (term_mem_138 c x hC hP) (mem_add (term_mem_139 c x hC hP) (mem_add (term_mem_140 c x hC hP) (mem_add (term_mem_141 c x hC hP) (mem_add (term_mem_142 c x hC hP) (mem_add (term_mem_143 c x hC hP) (by simpa [sumIntervals, eval] using mem_const (0 : ℚ))))))))))))))))))))))))))
  exact mem_subset h
    (by norm_num [blockBound_05, sumIntervals, RatInterval.add, RatInterval.const, termBound_120, termBound_121, termBound_122, termBound_123, termBound_124, termBound_125, termBound_126, termBound_127, termBound_128, termBound_129, termBound_130, termBound_131, termBound_132, termBound_133, termBound_134, termBound_135, termBound_136, termBound_137, termBound_138, termBound_139, termBound_140, termBound_141, termBound_142, termBound_143])
    (by norm_num [blockBound_05, sumIntervals, RatInterval.add, RatInterval.const, termBound_120, termBound_121, termBound_122, termBound_123, termBound_124, termBound_125, termBound_126, termBound_127, termBound_128, termBound_129, termBound_130, termBound_131, termBound_132, termBound_133, termBound_134, termBound_135, termBound_136, termBound_137, termBound_138, termBound_139, termBound_140, termBound_141, termBound_142, termBound_143])

def block_06 : List TermIndex := [.t144, .t145, .t146, .t147, .t148, .t149, .t150, .t151, .t152, .t153, .t154, .t155, .t156, .t157, .t158, .t159, .t160, .t161, .t162, .t163, .t164, .t165, .t166, .t167]
private def blockBound_06 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem block_mem_06 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    blockBound_06.mem (formalHessianEntry exponents c 0 0 x block_06) := by
  have h : (sumIntervals [termBound_144, termBound_145, termBound_146, termBound_147, termBound_148, termBound_149, termBound_150, termBound_151, termBound_152, termBound_153, termBound_154, termBound_155, termBound_156, termBound_157, termBound_158, termBound_159, termBound_160, termBound_161, termBound_162, termBound_163, termBound_164, termBound_165, termBound_166, termBound_167]).mem
      (formalHessianEntry exponents c 0 0 x block_06) := by
    exact (mem_add (term_mem_144 c x hC hP) (mem_add (term_mem_145 c x hC hP) (mem_add (term_mem_146 c x hC hP) (mem_add (term_mem_147 c x hC hP) (mem_add (term_mem_148 c x hC hP) (mem_add (term_mem_149 c x hC hP) (mem_add (term_mem_150 c x hC hP) (mem_add (term_mem_151 c x hC hP) (mem_add (term_mem_152 c x hC hP) (mem_add (term_mem_153 c x hC hP) (mem_add (term_mem_154 c x hC hP) (mem_add (term_mem_155 c x hC hP) (mem_add (term_mem_156 c x hC hP) (mem_add (term_mem_157 c x hC hP) (mem_add (term_mem_158 c x hC hP) (mem_add (term_mem_159 c x hC hP) (mem_add (term_mem_160 c x hC hP) (mem_add (term_mem_161 c x hC hP) (mem_add (term_mem_162 c x hC hP) (mem_add (term_mem_163 c x hC hP) (mem_add (term_mem_164 c x hC hP) (mem_add (term_mem_165 c x hC hP) (mem_add (term_mem_166 c x hC hP) (mem_add (term_mem_167 c x hC hP) (by simpa [sumIntervals, eval] using mem_const (0 : ℚ))))))))))))))))))))))))))
  exact mem_subset h
    (by norm_num [blockBound_06, sumIntervals, RatInterval.add, RatInterval.const, termBound_144, termBound_145, termBound_146, termBound_147, termBound_148, termBound_149, termBound_150, termBound_151, termBound_152, termBound_153, termBound_154, termBound_155, termBound_156, termBound_157, termBound_158, termBound_159, termBound_160, termBound_161, termBound_162, termBound_163, termBound_164, termBound_165, termBound_166, termBound_167])
    (by norm_num [blockBound_06, sumIntervals, RatInterval.add, RatInterval.const, termBound_144, termBound_145, termBound_146, termBound_147, termBound_148, termBound_149, termBound_150, termBound_151, termBound_152, termBound_153, termBound_154, termBound_155, termBound_156, termBound_157, termBound_158, termBound_159, termBound_160, termBound_161, termBound_162, termBound_163, termBound_164, termBound_165, termBound_166, termBound_167])

def block_07 : List TermIndex := [.t168, .t169, .t170, .t171, .t172, .t173, .t174, .t175, .t176, .t177, .t178, .t179, .t180, .t181, .t182, .t183, .t184, .t185, .t186, .t187, .t188, .t189, .t190, .t191]
private def blockBound_07 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem block_mem_07 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    blockBound_07.mem (formalHessianEntry exponents c 0 0 x block_07) := by
  have h : (sumIntervals [termBound_168, termBound_169, termBound_170, termBound_171, termBound_172, termBound_173, termBound_174, termBound_175, termBound_176, termBound_177, termBound_178, termBound_179, termBound_180, termBound_181, termBound_182, termBound_183, termBound_184, termBound_185, termBound_186, termBound_187, termBound_188, termBound_189, termBound_190, termBound_191]).mem
      (formalHessianEntry exponents c 0 0 x block_07) := by
    exact (mem_add (term_mem_168 c x hC hP) (mem_add (term_mem_169 c x hC hP) (mem_add (term_mem_170 c x hC hP) (mem_add (term_mem_171 c x hC hP) (mem_add (term_mem_172 c x hC hP) (mem_add (term_mem_173 c x hC hP) (mem_add (term_mem_174 c x hC hP) (mem_add (term_mem_175 c x hC hP) (mem_add (term_mem_176 c x hC hP) (mem_add (term_mem_177 c x hC hP) (mem_add (term_mem_178 c x hC hP) (mem_add (term_mem_179 c x hC hP) (mem_add (term_mem_180 c x hC hP) (mem_add (term_mem_181 c x hC hP) (mem_add (term_mem_182 c x hC hP) (mem_add (term_mem_183 c x hC hP) (mem_add (term_mem_184 c x hC hP) (mem_add (term_mem_185 c x hC hP) (mem_add (term_mem_186 c x hC hP) (mem_add (term_mem_187 c x hC hP) (mem_add (term_mem_188 c x hC hP) (mem_add (term_mem_189 c x hC hP) (mem_add (term_mem_190 c x hC hP) (mem_add (term_mem_191 c x hC hP) (by simpa [sumIntervals, eval] using mem_const (0 : ℚ))))))))))))))))))))))))))
  exact mem_subset h
    (by norm_num [blockBound_07, sumIntervals, RatInterval.add, RatInterval.const, termBound_168, termBound_169, termBound_170, termBound_171, termBound_172, termBound_173, termBound_174, termBound_175, termBound_176, termBound_177, termBound_178, termBound_179, termBound_180, termBound_181, termBound_182, termBound_183, termBound_184, termBound_185, termBound_186, termBound_187, termBound_188, termBound_189, termBound_190, termBound_191])
    (by norm_num [blockBound_07, sumIntervals, RatInterval.add, RatInterval.const, termBound_168, termBound_169, termBound_170, termBound_171, termBound_172, termBound_173, termBound_174, termBound_175, termBound_176, termBound_177, termBound_178, termBound_179, termBound_180, termBound_181, termBound_182, termBound_183, termBound_184, termBound_185, termBound_186, termBound_187, termBound_188, termBound_189, termBound_190, termBound_191])

def chunkTerms_01 : List TermIndex :=
  block_04 ++ (block_05 ++ (block_06 ++ (block_07 ++ ([]))))

def chunkInterval_01 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩

theorem chunk01_mem (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hx : ∀ j, (relativeBox j).mem (x j)) :
    chunkInterval_01.mem
      (formalHessianEntry exponents c 0 0 x chunkTerms_01) := by
  have hP := power_enclosures x hx
  have h : (sumIntervals [blockBound_04, blockBound_05, blockBound_06, blockBound_07]).mem
      (formalHessianEntry exponents c 0 0 x chunkTerms_01) := by
    simp only [chunkTerms_01, hessian_append, hessian_nil]
    exact (mem_add (block_mem_04 c x hC hP) (mem_add (block_mem_05 c x hC hP) (mem_add (block_mem_06 c x hC hP) (mem_add (block_mem_07 c x hC hP) (by simpa [sumIntervals, eval] using mem_const (0 : ℚ))))))
  exact mem_subset h
    (by norm_num [chunkInterval_01, sumIntervals, RatInterval.add, RatInterval.const, blockBound_04, blockBound_05, blockBound_06, blockBound_07])
    (by norm_num [chunkInterval_01, sumIntervals, RatInterval.add, RatInterval.const, blockBound_04, blockBound_05, blockBound_06, blockBound_07])

end ThomsonNine.LocalSparseHessianAAA
