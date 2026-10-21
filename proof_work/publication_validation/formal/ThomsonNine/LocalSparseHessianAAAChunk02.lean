import ThomsonNine.LocalSparseHessianAAABase

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace ThomsonNine.LocalSparseHessianAAA

open ThomsonNine.Interval ThomsonNine.Interval.SparsePolynomial
open ThomsonNine.Interval.RatInterval

private def termBound_192 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_192 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_192.mem (hessianTerm c x .t192) := by
  have hzero : hessianTerm c x .t192 = 0 := by
    unfold hessianTerm
    rw [show exponents .t192 = ![1, 3, 6] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_192, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_193 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_193 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_193.mem (hessianTerm c x .t193) := by
  have hzero : hessianTerm c x .t193 = 0 := by
    unfold hessianTerm
    rw [show exponents .t193 = ![1, 3, 7] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_193, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_194 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_194 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_194.mem (hessianTerm c x .t194) := by
  have hzero : hessianTerm c x .t194 = 0 := by
    unfold hessianTerm
    rw [show exponents .t194 = ![1, 3, 8] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_194, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_195 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_195 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_195.mem (hessianTerm c x .t195) := by
  have hzero : hessianTerm c x .t195 = 0 := by
    unfold hessianTerm
    rw [show exponents .t195 = ![1, 3, 9] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_195, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_196 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_196 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_196.mem (hessianTerm c x .t196) := by
  have hzero : hessianTerm c x .t196 = 0 := by
    unfold hessianTerm
    rw [show exponents .t196 = ![1, 4, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_196, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_197 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_197 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_197.mem (hessianTerm c x .t197) := by
  have hzero : hessianTerm c x .t197 = 0 := by
    unfold hessianTerm
    rw [show exponents .t197 = ![1, 4, 1] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_197, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_198 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_198 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_198.mem (hessianTerm c x .t198) := by
  have hzero : hessianTerm c x .t198 = 0 := by
    unfold hessianTerm
    rw [show exponents .t198 = ![1, 4, 2] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_198, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_199 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_199 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_199.mem (hessianTerm c x .t199) := by
  have hzero : hessianTerm c x .t199 = 0 := by
    unfold hessianTerm
    rw [show exponents .t199 = ![1, 4, 3] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_199, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_200 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_200 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_200.mem (hessianTerm c x .t200) := by
  have hzero : hessianTerm c x .t200 = 0 := by
    unfold hessianTerm
    rw [show exponents .t200 = ![1, 4, 4] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_200, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_201 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_201 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_201.mem (hessianTerm c x .t201) := by
  have hzero : hessianTerm c x .t201 = 0 := by
    unfold hessianTerm
    rw [show exponents .t201 = ![1, 4, 5] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_201, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_202 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_202 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_202.mem (hessianTerm c x .t202) := by
  have hzero : hessianTerm c x .t202 = 0 := by
    unfold hessianTerm
    rw [show exponents .t202 = ![1, 4, 6] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_202, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_203 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_203 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_203.mem (hessianTerm c x .t203) := by
  have hzero : hessianTerm c x .t203 = 0 := by
    unfold hessianTerm
    rw [show exponents .t203 = ![1, 4, 7] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_203, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_204 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_204 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_204.mem (hessianTerm c x .t204) := by
  have hzero : hessianTerm c x .t204 = 0 := by
    unfold hessianTerm
    rw [show exponents .t204 = ![1, 4, 8] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_204, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_205 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_205 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_205.mem (hessianTerm c x .t205) := by
  have hzero : hessianTerm c x .t205 = 0 := by
    unfold hessianTerm
    rw [show exponents .t205 = ![1, 4, 9] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_205, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_206 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_206 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_206.mem (hessianTerm c x .t206) := by
  have hzero : hessianTerm c x .t206 = 0 := by
    unfold hessianTerm
    rw [show exponents .t206 = ![1, 5, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_206, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_207 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_207 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_207.mem (hessianTerm c x .t207) := by
  have hzero : hessianTerm c x .t207 = 0 := by
    unfold hessianTerm
    rw [show exponents .t207 = ![1, 5, 1] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_207, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_208 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_208 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_208.mem (hessianTerm c x .t208) := by
  have hzero : hessianTerm c x .t208 = 0 := by
    unfold hessianTerm
    rw [show exponents .t208 = ![1, 5, 2] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_208, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_209 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_209 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_209.mem (hessianTerm c x .t209) := by
  have hzero : hessianTerm c x .t209 = 0 := by
    unfold hessianTerm
    rw [show exponents .t209 = ![1, 5, 3] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_209, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_210 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_210 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_210.mem (hessianTerm c x .t210) := by
  have hzero : hessianTerm c x .t210 = 0 := by
    unfold hessianTerm
    rw [show exponents .t210 = ![1, 5, 4] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_210, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_211 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_211 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_211.mem (hessianTerm c x .t211) := by
  have hzero : hessianTerm c x .t211 = 0 := by
    unfold hessianTerm
    rw [show exponents .t211 = ![1, 5, 5] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_211, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_212 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_212 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_212.mem (hessianTerm c x .t212) := by
  have hzero : hessianTerm c x .t212 = 0 := by
    unfold hessianTerm
    rw [show exponents .t212 = ![1, 5, 6] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_212, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_213 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_213 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_213.mem (hessianTerm c x .t213) := by
  have hzero : hessianTerm c x .t213 = 0 := by
    unfold hessianTerm
    rw [show exponents .t213 = ![1, 5, 7] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_213, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_214 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_214 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_214.mem (hessianTerm c x .t214) := by
  have hzero : hessianTerm c x .t214 = 0 := by
    unfold hessianTerm
    rw [show exponents .t214 = ![1, 5, 8] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_214, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_215 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_215 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_215.mem (hessianTerm c x .t215) := by
  have hzero : hessianTerm c x .t215 = 0 := by
    unfold hessianTerm
    rw [show exponents .t215 = ![1, 5, 9] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_215, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_216 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_216 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_216.mem (hessianTerm c x .t216) := by
  have hzero : hessianTerm c x .t216 = 0 := by
    unfold hessianTerm
    rw [show exponents .t216 = ![1, 6, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_216, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_217 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_217 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_217.mem (hessianTerm c x .t217) := by
  have hzero : hessianTerm c x .t217 = 0 := by
    unfold hessianTerm
    rw [show exponents .t217 = ![1, 6, 1] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_217, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_218 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_218 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_218.mem (hessianTerm c x .t218) := by
  have hzero : hessianTerm c x .t218 = 0 := by
    unfold hessianTerm
    rw [show exponents .t218 = ![1, 6, 2] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_218, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_219 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_219 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_219.mem (hessianTerm c x .t219) := by
  have hzero : hessianTerm c x .t219 = 0 := by
    unfold hessianTerm
    rw [show exponents .t219 = ![1, 6, 3] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_219, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_220 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_220 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_220.mem (hessianTerm c x .t220) := by
  have hzero : hessianTerm c x .t220 = 0 := by
    unfold hessianTerm
    rw [show exponents .t220 = ![1, 6, 4] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_220, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_221 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_221 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_221.mem (hessianTerm c x .t221) := by
  have hzero : hessianTerm c x .t221 = 0 := by
    unfold hessianTerm
    rw [show exponents .t221 = ![1, 6, 5] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_221, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_222 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_222 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_222.mem (hessianTerm c x .t222) := by
  have hzero : hessianTerm c x .t222 = 0 := by
    unfold hessianTerm
    rw [show exponents .t222 = ![1, 6, 6] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_222, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_223 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_223 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_223.mem (hessianTerm c x .t223) := by
  have hzero : hessianTerm c x .t223 = 0 := by
    unfold hessianTerm
    rw [show exponents .t223 = ![1, 6, 7] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_223, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_224 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_224 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_224.mem (hessianTerm c x .t224) := by
  have hzero : hessianTerm c x .t224 = 0 := by
    unfold hessianTerm
    rw [show exponents .t224 = ![1, 6, 8] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_224, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_225 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_225 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_225.mem (hessianTerm c x .t225) := by
  have hzero : hessianTerm c x .t225 = 0 := by
    unfold hessianTerm
    rw [show exponents .t225 = ![1, 6, 9] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_225, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_226 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_226 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_226.mem (hessianTerm c x .t226) := by
  have hzero : hessianTerm c x .t226 = 0 := by
    unfold hessianTerm
    rw [show exponents .t226 = ![1, 7, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_226, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_227 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_227 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_227.mem (hessianTerm c x .t227) := by
  have hzero : hessianTerm c x .t227 = 0 := by
    unfold hessianTerm
    rw [show exponents .t227 = ![1, 7, 1] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_227, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_228 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_228 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_228.mem (hessianTerm c x .t228) := by
  have hzero : hessianTerm c x .t228 = 0 := by
    unfold hessianTerm
    rw [show exponents .t228 = ![1, 7, 2] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_228, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_229 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_229 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_229.mem (hessianTerm c x .t229) := by
  have hzero : hessianTerm c x .t229 = 0 := by
    unfold hessianTerm
    rw [show exponents .t229 = ![1, 7, 3] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_229, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_230 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_230 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_230.mem (hessianTerm c x .t230) := by
  have hzero : hessianTerm c x .t230 = 0 := by
    unfold hessianTerm
    rw [show exponents .t230 = ![1, 7, 4] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_230, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_231 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_231 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_231.mem (hessianTerm c x .t231) := by
  have hzero : hessianTerm c x .t231 = 0 := by
    unfold hessianTerm
    rw [show exponents .t231 = ![1, 7, 5] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_231, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_232 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_232 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_232.mem (hessianTerm c x .t232) := by
  have hzero : hessianTerm c x .t232 = 0 := by
    unfold hessianTerm
    rw [show exponents .t232 = ![1, 7, 6] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_232, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_233 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_233 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_233.mem (hessianTerm c x .t233) := by
  have hzero : hessianTerm c x .t233 = 0 := by
    unfold hessianTerm
    rw [show exponents .t233 = ![1, 7, 7] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_233, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_234 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_234 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_234.mem (hessianTerm c x .t234) := by
  have hzero : hessianTerm c x .t234 = 0 := by
    unfold hessianTerm
    rw [show exponents .t234 = ![1, 7, 8] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_234, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_235 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_235 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_235.mem (hessianTerm c x .t235) := by
  have hzero : hessianTerm c x .t235 = 0 := by
    unfold hessianTerm
    rw [show exponents .t235 = ![1, 7, 9] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_235, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_236 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_236 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_236.mem (hessianTerm c x .t236) := by
  have hzero : hessianTerm c x .t236 = 0 := by
    unfold hessianTerm
    rw [show exponents .t236 = ![1, 8, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_236, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_237 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_237 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_237.mem (hessianTerm c x .t237) := by
  have hzero : hessianTerm c x .t237 = 0 := by
    unfold hessianTerm
    rw [show exponents .t237 = ![1, 8, 1] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_237, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_238 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_238 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_238.mem (hessianTerm c x .t238) := by
  have hzero : hessianTerm c x .t238 = 0 := by
    unfold hessianTerm
    rw [show exponents .t238 = ![1, 8, 2] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_238, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_239 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_239 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_239.mem (hessianTerm c x .t239) := by
  have hzero : hessianTerm c x .t239 = 0 := by
    unfold hessianTerm
    rw [show exponents .t239 = ![1, 8, 3] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_239, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_240 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_240 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_240.mem (hessianTerm c x .t240) := by
  have hzero : hessianTerm c x .t240 = 0 := by
    unfold hessianTerm
    rw [show exponents .t240 = ![1, 8, 4] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_240, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_241 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_241 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_241.mem (hessianTerm c x .t241) := by
  have hzero : hessianTerm c x .t241 = 0 := by
    unfold hessianTerm
    rw [show exponents .t241 = ![1, 8, 5] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_241, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_242 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_242 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_242.mem (hessianTerm c x .t242) := by
  have hzero : hessianTerm c x .t242 = 0 := by
    unfold hessianTerm
    rw [show exponents .t242 = ![1, 8, 6] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_242, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_243 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_243 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_243.mem (hessianTerm c x .t243) := by
  have hzero : hessianTerm c x .t243 = 0 := by
    unfold hessianTerm
    rw [show exponents .t243 = ![1, 8, 7] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_243, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_244 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_244 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_244.mem (hessianTerm c x .t244) := by
  have hzero : hessianTerm c x .t244 = 0 := by
    unfold hessianTerm
    rw [show exponents .t244 = ![1, 8, 8] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_244, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_245 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_245 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_245.mem (hessianTerm c x .t245) := by
  have hzero : hessianTerm c x .t245 = 0 := by
    unfold hessianTerm
    rw [show exponents .t245 = ![1, 8, 9] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_245, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_246 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_246 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_246.mem (hessianTerm c x .t246) := by
  have hzero : hessianTerm c x .t246 = 0 := by
    unfold hessianTerm
    rw [show exponents .t246 = ![1, 9, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_246, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_247 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_247 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_247.mem (hessianTerm c x .t247) := by
  have hzero : hessianTerm c x .t247 = 0 := by
    unfold hessianTerm
    rw [show exponents .t247 = ![1, 9, 1] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_247, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_248 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_248 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_248.mem (hessianTerm c x .t248) := by
  have hzero : hessianTerm c x .t248 = 0 := by
    unfold hessianTerm
    rw [show exponents .t248 = ![1, 9, 2] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_248, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_249 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_249 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_249.mem (hessianTerm c x .t249) := by
  have hzero : hessianTerm c x .t249 = 0 := by
    unfold hessianTerm
    rw [show exponents .t249 = ![1, 9, 3] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_249, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_250 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_250 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_250.mem (hessianTerm c x .t250) := by
  have hzero : hessianTerm c x .t250 = 0 := by
    unfold hessianTerm
    rw [show exponents .t250 = ![1, 9, 4] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_250, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_251 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_251 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_251.mem (hessianTerm c x .t251) := by
  have hzero : hessianTerm c x .t251 = 0 := by
    unfold hessianTerm
    rw [show exponents .t251 = ![1, 9, 5] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_251, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_252 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_252 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_252.mem (hessianTerm c x .t252) := by
  have hzero : hessianTerm c x .t252 = 0 := by
    unfold hessianTerm
    rw [show exponents .t252 = ![1, 9, 6] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_252, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_253 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_253 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_253.mem (hessianTerm c x .t253) := by
  have hzero : hessianTerm c x .t253 = 0 := by
    unfold hessianTerm
    rw [show exponents .t253 = ![1, 9, 7] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_253, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_254 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_254 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_254.mem (hessianTerm c x .t254) := by
  have hzero : hessianTerm c x .t254 = 0 := by
    unfold hessianTerm
    rw [show exponents .t254 = ![1, 9, 8] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_254, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_255 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_255 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_255.mem (hessianTerm c x .t255) := by
  have hzero : hessianTerm c x .t255 = 0 := by
    unfold hessianTerm
    rw [show exponents .t255 = ![1, 9, 9] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_255, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_256 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem term_mem_256 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_256.mem (hessianTerm c x .t256) := by
  have hzero : hessianTerm c x .t256 = 0 := by
    unfold hessianTerm
    rw [show exponents .t256 = ![1, 10, 0] from rfl]
    simp [lowerExponent, derivativeCoeff]
  rw [hzero]
  simpa [termBound_256, RatInterval.const] using mem_const (0 : ℚ)

private def termBound_257 : RatInterval := ⟨(95930805682687374842511712589902252154387279176474821647541171015679777027498289485323150541107528297046516515742952909297541667118363884451830222129143888467644844685948254624644712410744677 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ), (95930805682687374842511712589902252154387279176474821647541171015679777027498289485323150541107528297046516515742952909297541681894544169473014218771754823389967522934974740721848206800003753 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ), by norm_num⟩
private def qAlo_257 : ℚ := (95930805682687374842511712589902252154387279176474821647541171015679777027498289485323150541107528297046516515742952909297541667118363884451830222129143888467644844685948254624644712410744677 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qAhi_257 : ℚ := (95930805682687374842511712589902252154387279176474821647541171015679777027498289485323150541107528297046516515742952909297541681894544169473014218771754823389967522934974740721848206800003753 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qIlo_257 : ℚ := (95930805682687374842511712589902252154387279176474821647541171015679777027498289485323150541107528297046516515742952909297541667118363884451830222129143888467644844685948254624644712410744677 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def qIhi_257 : ℚ := (95930805682687374842511712589902252154387279176474821647541171015679777027498289485323150541107528297046516515742952909297541681894544169473014218771754823389967522934974740721848206800003753 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def I_257 : RatInterval :=
  { lo := qIlo_257, hi := qIhi_257, h := by rw [Rat.le_iff]; norm_num [qIlo_257, qIhi_257] }
private theorem term_mem_257 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_257.mem (hessianTerm c x .t257) := by
  have hterm : hessianTerm c x .t257 =
      (c .t257 * 2) * (1) := by
    unfold hessianTerm derivativeCoeff monomial
    rw [show exponents .t257 = ![2, 0, 0] from rfl]
    norm_num [lowerExponent]
    try ring
    try simp
  rw [hterm]
  have hcI : I_257.mem (c .t257 * 2) := by
    constructor
    · have h := (hC .t257).1
      rw [show (coefficientInterval .t257).lo = qAlo_257 from rfl] at h
      norm_num [I_257, qIlo_257, qAlo_257] at h ⊢
      linarith
    · have h := (hC .t257).2
      rw [show (coefficientInterval .t257).hi = qAhi_257 from rfl] at h
      norm_num [I_257, qIhi_257, qAhi_257] at h ⊢
      linarith
  have hJmem : (RatInterval.const 1).mem (1 : ℝ) := by
    simpa using mem_const (1 : ℚ)
  have hmain : termBound_257.mem ((c .t257 * 2) * (1 : ℝ)) := by
    refine mem_mul_of_bounds hcI hJmem ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [I_257, termBound_257, RatInterval.const]
      rw [Rat.le_iff]
      norm_num [qIlo_257, qIhi_257]
  simpa using hmain

private def termBound_258 : RatInterval := ⟨(-451251652923162259766125629629237713565133908125687626875816441942475903036417404422672309307303369785713997275713326872768593314671594305636982112215116462086939186224093285784350192243385 / 1140610154405548804660292901425072831223307126812139982644798129474818791802169346626478202829342849944660577393398601827672176180343859499563165329930553547062998668590066237520718548061650944 : ℚ), (451251652923162259766125629629237713565133908125687626875816441942475903036417404422672309307303369785933735253119037756938162543738357984505746399592213580220818331326444476130852252282883 / 1140610154405548804660292901425072831223307126812139982644798129474818791802169346626478202829342849944660577393398601827672176180343859499563165329930553547062998668590066237520718548061650944 : ℚ), by norm_num⟩
private def qAlo_258 : ℚ := (-225625826461581129883062814814618856782566954062843813437908220971237951518208702211336154653651684892820594475002575353328282281950926479366502500487397837098897460366697144521052220246744197 / 1140610154405548804660292901425072831223307126812139982644798129474818791802169346626478202829342849944660577393398601827672176180343859499563165329930553547062998668590066237520718548061650944 : ℚ)
private def qAhi_258 : ℚ := (-902503305846324519532251259258475427130267816251375253751632883884951806072834808845344618614606739571282377900010301413313129123927215316162208287401583962909871569229481988198418037253443405 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qIlo_258 : ℚ := (-225625826461581129883062814814618856782566954062843813437908220971237951518208702211336154653651684892820594475002575353328282281950926479366502500487397837098897460366697144521052220246744197 / 570305077202774402330146450712536415611653563406069991322399064737409395901084673313239101414671424972330288696699300913836088090171929749781582664965276773531499334295033118760359274030825472 : ℚ)
private def qIhi_258 : ℚ := (-902503305846324519532251259258475427130267816251375253751632883884951806072834808845344618614606739571282377900010301413313129123927215316162208287401583962909871569229481988198418037253443405 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def I_258 : RatInterval :=
  { lo := qIlo_258, hi := qIhi_258, h := by rw [Rat.le_iff]; norm_num [qIlo_258, qIhi_258] }
private theorem term_mem_258 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_258.mem (hessianTerm c x .t258) := by
  have hterm : hessianTerm c x .t258 =
      (c .t258 * 2) * ((x 2 ^ 1)) := by
    unfold hessianTerm derivativeCoeff monomial
    rw [show exponents .t258 = ![2, 0, 1] from rfl]
    norm_num [lowerExponent]
    try ring
    try simp
  rw [hterm]
  have hcI : I_258.mem (c .t258 * 2) := by
    constructor
    · have h := (hC .t258).1
      rw [show (coefficientInterval .t258).lo = qAlo_258 from rfl] at h
      norm_num [I_258, qIlo_258, qAlo_258] at h ⊢
      linarith
    · have h := (hC .t258).2
      rw [show (coefficientInterval .t258).hi = qAhi_258 from rfl] at h
      norm_num [I_258, qIhi_258, qAhi_258] at h ⊢
      linarith
  have hJmem : power_01.mem (x 2 ^ 1) := by
    simpa [powerTable, finitePower, power_01] using hP 2 1
  have hmain : termBound_258.mem ((c .t258 * 2) * ((x 2 ^ 1))) := by
    refine mem_mul_of_bounds hcI hJmem ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [I_258, power_01, termBound_258]
      rw [Rat.le_iff]
      norm_num [qIlo_258, qIhi_258]
  simpa using hmain

private def termBound_259 : RatInterval := ⟨(0 : ℚ), (336140994838695086537509790518153000088439943082115347221299528182265759891534691057708854866626519005858655578547370606375045968971926726755605471673165582657265597332961067314943220021 / 142576269300693600582536612678134103902913390851517497830599766184352348975271168328309775353667856243082572174174825228459022022542982437445395666241319193382874833573758279690089818507706368 : ℚ), by norm_num⟩
private def qAlo_259 : ℚ := (5378255917419121384600156648290448001415039089313845555540792450916252158264555056923341677866024304086765046054282778776265903312991162935857689284068740100976496843397220838338065597789398795 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qAhi_259 : ℚ := (5378255917419121384600156648290448001415039089313845555540792450916252158264555056923341677866024304086765046054282778776265903321362753016280483983273920495985209056618217600080660948551096193 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qIlo_259 : ℚ := (5378255917419121384600156648290448001415039089313845555540792450916252158264555056923341677866024304086765046054282778776265903312991162935857689284068740100976496843397220838338065597789398795 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def qIhi_259 : ℚ := (5378255917419121384600156648290448001415039089313845555540792450916252158264555056923341677866024304086765046054282778776265903321362753016280483983273920495985209056618217600080660948551096193 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def I_259 : RatInterval :=
  { lo := qIlo_259, hi := qIhi_259, h := by rw [Rat.le_iff]; norm_num [qIlo_259, qIhi_259] }
private theorem term_mem_259 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_259.mem (hessianTerm c x .t259) := by
  have hterm : hessianTerm c x .t259 =
      (c .t259 * 2) * ((x 2 ^ 2)) := by
    unfold hessianTerm derivativeCoeff monomial
    rw [show exponents .t259 = ![2, 0, 2] from rfl]
    norm_num [lowerExponent]
    try ring
    try simp
  rw [hterm]
  have hcI : I_259.mem (c .t259 * 2) := by
    constructor
    · have h := (hC .t259).1
      rw [show (coefficientInterval .t259).lo = qAlo_259 from rfl] at h
      norm_num [I_259, qIlo_259, qAlo_259] at h ⊢
      linarith
    · have h := (hC .t259).2
      rw [show (coefficientInterval .t259).hi = qAhi_259 from rfl] at h
      norm_num [I_259, qIhi_259, qAhi_259] at h ⊢
      linarith
  have hJmem : power_02.mem (x 2 ^ 2) := by
    simpa [powerTable, finitePower, power_02] using hP 2 2
  have hmain : termBound_259.mem ((c .t259 * 2) * ((x 2 ^ 2))) := by
    refine mem_mul_of_bounds hcI hJmem ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [I_259, power_02, termBound_259]
      rw [Rat.le_iff]
      norm_num [qIlo_259, qIhi_259]
  simpa using hmain

private def termBound_260 : RatInterval := ⟨(-23764802942918154536382679628950800643957374677618211436250066637841554936124589918606112419673851332133303716441046453489694011121111947581528830331542883575506964785815677937958268929 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ), (11882401471459077268191339814475400321978687338809105718125033318920777468062294959303056209836925666060865696886493374347213842952153777701305853048527366479184343759283409569715045839 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ), by norm_num⟩
private def qAlo_260 : ℚ := (11882401471459077268191339814475400321978687338809105718125033318920777468062294959303056209836925666043541786932769251851960601819626153382761640001695001445226862877398568523253383088698357413 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qAhi_260 : ℚ := (1485300183932384658523917476809425040247335917351138214765629164865097183507786869912882026229615708255442723366596156481495075228995037048471699532519711666928410586713229733469197476361247477 / 570305077202774402330146450712536415611653563406069991322399064737409395901084673313239101414671424972330288696699300913836088090171929749781582664965276773531499334295033118760359274030825472 : ℚ)
private def qIlo_260 : ℚ := (11882401471459077268191339814475400321978687338809105718125033318920777468062294959303056209836925666043541786932769251851960601819626153382761640001695001445226862877398568523253383088698357413 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def qIhi_260 : ℚ := (1485300183932384658523917476809425040247335917351138214765629164865097183507786869912882026229615708255442723366596156481495075228995037048471699532519711666928410586713229733469197476361247477 / 285152538601387201165073225356268207805826781703034995661199532368704697950542336656619550707335712486165144348349650456918044045085964874890791332482638386765749667147516559380179637015412736 : ℚ)
private def I_260 : RatInterval :=
  { lo := qIlo_260, hi := qIhi_260, h := by rw [Rat.le_iff]; norm_num [qIlo_260, qIhi_260] }
private theorem term_mem_260 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_260.mem (hessianTerm c x .t260) := by
  have hterm : hessianTerm c x .t260 =
      (c .t260 * 2) * ((x 2 ^ 3)) := by
    unfold hessianTerm derivativeCoeff monomial
    rw [show exponents .t260 = ![2, 0, 3] from rfl]
    norm_num [lowerExponent]
    try ring
    try simp
  rw [hterm]
  have hcI : I_260.mem (c .t260 * 2) := by
    constructor
    · have h := (hC .t260).1
      rw [show (coefficientInterval .t260).lo = qAlo_260 from rfl] at h
      norm_num [I_260, qIlo_260, qAlo_260] at h ⊢
      linarith
    · have h := (hC .t260).2
      rw [show (coefficientInterval .t260).hi = qAhi_260 from rfl] at h
      norm_num [I_260, qIhi_260, qAhi_260] at h ⊢
      linarith
  have hJmem : power_03.mem (x 2 ^ 3) := by
    simpa [powerTable, finitePower, power_03] using hP 2 3
  have hmain : termBound_260.mem ((c .t260 * 2) * ((x 2 ^ 3))) := by
    refine mem_mul_of_bounds hcI hJmem ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [I_260, power_03, termBound_260]
      rw [Rat.le_iff]
      norm_num [qIlo_260, qIhi_260]
  simpa using hmain

private def termBound_261 : RatInterval := ⟨(-28779316146597540878259907337612589275692182559807850752384373383248864141330762896802790664899352392874878666583408246584451838293604637545209972259894263264210503429694167754268725 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ), (0 : ℚ), by norm_num⟩
private def qAlo_261 : ℚ := (-14389658073298770439129953668806294637846091279903925376192186691624432070665381448401395332449676196400124090276886768096179320969529914914869209108094285267868825426716106364753934686377114063 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qAhi_261 : ℚ := (-3597414518324692609782488417201573659461522819975981344048046672906108017666345362100348833112419049100031022569221692024044830239123977939355512439894056198204852066230107453808783863213546129 / 1140610154405548804660292901425072831223307126812139982644798129474818791802169346626478202829342849944660577393398601827672176180343859499563165329930553547062998668590066237520718548061650944 : ℚ)
private def qIlo_261 : ℚ := (-14389658073298770439129953668806294637846091279903925376192186691624432070665381448401395332449676196400124090276886768096179320969529914914869209108094285267868825426716106364753934686377114063 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def qIhi_261 : ℚ := (-3597414518324692609782488417201573659461522819975981344048046672906108017666345362100348833112419049100031022569221692024044830239123977939355512439894056198204852066230107453808783863213546129 / 570305077202774402330146450712536415611653563406069991322399064737409395901084673313239101414671424972330288696699300913836088090171929749781582664965276773531499334295033118760359274030825472 : ℚ)
private def I_261 : RatInterval :=
  { lo := qIlo_261, hi := qIhi_261, h := by rw [Rat.le_iff]; norm_num [qIlo_261, qIhi_261] }
private theorem term_mem_261 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_261.mem (hessianTerm c x .t261) := by
  have hterm : hessianTerm c x .t261 =
      (c .t261 * 2) * ((x 2 ^ 4)) := by
    unfold hessianTerm derivativeCoeff monomial
    rw [show exponents .t261 = ![2, 0, 4] from rfl]
    norm_num [lowerExponent]
    try ring
    try simp
  rw [hterm]
  have hcI : I_261.mem (c .t261 * 2) := by
    constructor
    · have h := (hC .t261).1
      rw [show (coefficientInterval .t261).lo = qAlo_261 from rfl] at h
      norm_num [I_261, qIlo_261, qAlo_261] at h ⊢
      linarith
    · have h := (hC .t261).2
      rw [show (coefficientInterval .t261).hi = qAhi_261 from rfl] at h
      norm_num [I_261, qIhi_261, qAhi_261] at h ⊢
      linarith
  have hJmem : power_04.mem (x 2 ^ 4) := by
    simpa [powerTable, finitePower, power_04] using hP 2 4
  have hmain : termBound_261.mem ((c .t261 * 2) * ((x 2 ^ 4))) := by
    refine mem_mul_of_bounds hcI hJmem ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [I_261, power_04, termBound_261]
      rw [Rat.le_iff]
      norm_num [qIlo_261, qIhi_261]
  simpa using hmain

private def termBound_262 : RatInterval := ⟨(-95363375366650614767526050364645200340874073293645404423466461608769562755026394862902019874024538170258837212569292263230174796957535856326793572265174682807665283999129527921883 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ), (23840843841662653691881512591161300085218518323411351105866615402192390688756598715725504968506134542576318654092012298227067520098064527553986986056324833391988815504750998725347 / 1140610154405548804660292901425072831223307126812139982644798129474818791802169346626478202829342849944660577393398601827672176180343859499563165329930553547062998668590066237520718548061650944 : ℚ), by norm_num⟩
private def qAlo_262 : ℚ := (-47681687683325307383763025182322600170437036646822702211733230804384781377513197431451009937012269084998077193360877453602333112759631535807282692151146247463293409467835256782976018867017740811 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qAhi_262 : ℚ := (-23840843841662653691881512591161300085218518323411351105866615402192390688756598715725504968506134542499038596680438726801166556374585208179805379926098004516419252446325926571378847677027727497 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def qIlo_262 : ℚ := (-47681687683325307383763025182322600170437036646822702211733230804384781377513197431451009937012269084998077193360877453602333112759631535807282692151146247463293409467835256782976018867017740811 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def qIhi_262 : ℚ := (-23840843841662653691881512591161300085218518323411351105866615402192390688756598715725504968506134542499038596680438726801166556374585208179805379926098004516419252446325926571378847677027727497 / 1140610154405548804660292901425072831223307126812139982644798129474818791802169346626478202829342849944660577393398601827672176180343859499563165329930553547062998668590066237520718548061650944 : ℚ)
private def I_262 : RatInterval :=
  { lo := qIlo_262, hi := qIhi_262, h := by rw [Rat.le_iff]; norm_num [qIlo_262, qIhi_262] }
private theorem term_mem_262 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_262.mem (hessianTerm c x .t262) := by
  have hterm : hessianTerm c x .t262 =
      (c .t262 * 2) * ((x 2 ^ 5)) := by
    unfold hessianTerm derivativeCoeff monomial
    rw [show exponents .t262 = ![2, 0, 5] from rfl]
    norm_num [lowerExponent]
    try ring
    try simp
  rw [hterm]
  have hcI : I_262.mem (c .t262 * 2) := by
    constructor
    · have h := (hC .t262).1
      rw [show (coefficientInterval .t262).lo = qAlo_262 from rfl] at h
      norm_num [I_262, qIlo_262, qAlo_262] at h ⊢
      linarith
    · have h := (hC .t262).2
      rw [show (coefficientInterval .t262).hi = qAhi_262 from rfl] at h
      norm_num [I_262, qIhi_262, qAhi_262] at h ⊢
      linarith
  have hJmem : power_05.mem (x 2 ^ 5) := by
    simpa [powerTable, finitePower, power_05] using hP 2 5
  have hmain : termBound_262.mem ((c .t262 * 2) * ((x 2 ^ 5))) := by
    refine mem_mul_of_bounds hcI hJmem ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [I_262, power_05, termBound_262]
      rw [Rat.le_iff]
      norm_num [qIlo_262, qIhi_262]
  simpa using hmain

private def termBound_263 : RatInterval := ⟨(-13603089104499751761006773069669309429194506420829598479495978689160006562595402491754375191468646553067037329818171414267624655639685743363177626761880097975135110128792812641 / 1140610154405548804660292901425072831223307126812139982644798129474818791802169346626478202829342849944660577393398601827672176180343859499563165329930553547062998668590066237520718548061650944 : ℚ), (0 : ℚ), by norm_num⟩
private def qAlo_263 : ℚ := (-27206178208999503522013546139338618858389012841659196958991957378320013125190804983508750382937293106028248119540468970280617391642761914228858166971212577832079182334798151280495090872805970383 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qAhi_263 : ℚ := (-6801544552249875880503386534834654714597253210414799239747989344580003281297701245877187595734323276507062029885117242570154347909189609695822444279958365784139773333679101297032510906493316513 / 1140610154405548804660292901425072831223307126812139982644798129474818791802169346626478202829342849944660577393398601827672176180343859499563165329930553547062998668590066237520718548061650944 : ℚ)
private def qIlo_263 : ℚ := (-27206178208999503522013546139338618858389012841659196958991957378320013125190804983508750382937293106028248119540468970280617391642761914228858166971212577832079182334798151280495090872805970383 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def qIhi_263 : ℚ := (-6801544552249875880503386534834654714597253210414799239747989344580003281297701245877187595734323276507062029885117242570154347909189609695822444279958365784139773333679101297032510906493316513 / 570305077202774402330146450712536415611653563406069991322399064737409395901084673313239101414671424972330288696699300913836088090171929749781582664965276773531499334295033118760359274030825472 : ℚ)
private def I_263 : RatInterval :=
  { lo := qIlo_263, hi := qIhi_263, h := by rw [Rat.le_iff]; norm_num [qIlo_263, qIhi_263] }
private theorem term_mem_263 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_263.mem (hessianTerm c x .t263) := by
  have hterm : hessianTerm c x .t263 =
      (c .t263 * 2) * ((x 2 ^ 6)) := by
    unfold hessianTerm derivativeCoeff monomial
    rw [show exponents .t263 = ![2, 0, 6] from rfl]
    norm_num [lowerExponent]
    try ring
    try simp
  rw [hterm]
  have hcI : I_263.mem (c .t263 * 2) := by
    constructor
    · have h := (hC .t263).1
      rw [show (coefficientInterval .t263).lo = qAlo_263 from rfl] at h
      norm_num [I_263, qIlo_263, qAlo_263] at h ⊢
      linarith
    · have h := (hC .t263).2
      rw [show (coefficientInterval .t263).hi = qAhi_263 from rfl] at h
      norm_num [I_263, qIhi_263, qAhi_263] at h ⊢
      linarith
  have hJmem : power_06.mem (x 2 ^ 6) := by
    simpa [powerTable, finitePower, power_06] using hP 2 6
  have hmain : termBound_263.mem ((c .t263 * 2) * ((x 2 ^ 6))) := by
    refine mem_mul_of_bounds hcI hJmem ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [I_263, power_06, termBound_263]
      rw [Rat.le_iff]
      norm_num [qIlo_263, qIhi_263]
  simpa using hmain

private def termBound_264 : RatInterval := ⟨(-87787526473306075462801485816767105384700055330180696791564469493570118862995161680812613119803096612296207324267429671010597179002419384079785987947473121015661388947945485 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ), (10973440809163259432850185727095888173087506916272587098945558686696264857874395210101576639975387076531682374578028801066061593718117512472962815996667680799265485148035397 / 570305077202774402330146450712536415611653563406069991322399064737409395901084673313239101414671424972330288696699300913836088090171929749781582664965276773531499334295033118760359274030825472 : ℚ), by norm_num⟩
private def qAlo_264 : ℚ := (43893763236653037731400742908383552692350027665090348395782234746785059431497580840406306559901548305948909472882114970696457588303407928231646545008833926192144518765181145959850987072407558531 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qAhi_264 : ℚ := (10973440809163259432850185727095888173087506916272587098945558686696264857874395210101576639975387076487227368220528742674114397076520866789363427404709543272772242699775427814326717321955568399 / 1140610154405548804660292901425072831223307126812139982644798129474818791802169346626478202829342849944660577393398601827672176180343859499563165329930553547062998668590066237520718548061650944 : ℚ)
private def qIlo_264 : ℚ := (43893763236653037731400742908383552692350027665090348395782234746785059431497580840406306559901548305948909472882114970696457588303407928231646545008833926192144518765181145959850987072407558531 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def qIhi_264 : ℚ := (10973440809163259432850185727095888173087506916272587098945558686696264857874395210101576639975387076487227368220528742674114397076520866789363427404709543272772242699775427814326717321955568399 / 570305077202774402330146450712536415611653563406069991322399064737409395901084673313239101414671424972330288696699300913836088090171929749781582664965276773531499334295033118760359274030825472 : ℚ)
private def I_264 : RatInterval :=
  { lo := qIlo_264, hi := qIhi_264, h := by rw [Rat.le_iff]; norm_num [qIlo_264, qIhi_264] }
private theorem term_mem_264 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_264.mem (hessianTerm c x .t264) := by
  have hterm : hessianTerm c x .t264 =
      (c .t264 * 2) * ((x 2 ^ 7)) := by
    unfold hessianTerm derivativeCoeff monomial
    rw [show exponents .t264 = ![2, 0, 7] from rfl]
    norm_num [lowerExponent]
    try ring
    try simp
  rw [hterm]
  have hcI : I_264.mem (c .t264 * 2) := by
    constructor
    · have h := (hC .t264).1
      rw [show (coefficientInterval .t264).lo = qAlo_264 from rfl] at h
      norm_num [I_264, qIlo_264, qAlo_264] at h ⊢
      linarith
    · have h := (hC .t264).2
      rw [show (coefficientInterval .t264).hi = qAhi_264 from rfl] at h
      norm_num [I_264, qIhi_264, qAhi_264] at h ⊢
      linarith
  have hJmem : power_07.mem (x 2 ^ 7) := by
    simpa [powerTable, finitePower, power_07] using hP 2 7
  have hmain : termBound_264.mem ((c .t264 * 2) * ((x 2 ^ 7))) := by
    refine mem_mul_of_bounds hcI hJmem ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [I_264, power_07, termBound_264]
      rw [Rat.le_iff]
      norm_num [qIlo_264, qIhi_264]
  simpa using hmain

private def termBound_265 : RatInterval := ⟨(0 : ℚ), (12560496339058254579012729685630563076554629718304979677268215346580787866725650860506985012074000413249664727425240349317162126470315450628952148596523529288772665999297 / 285152538601387201165073225356268207805826781703034995661199532368704697950542336656619550707335712486165144348349650456918044045085964874890791332482638386765749667147516559380179637015412736 : ℚ), by norm_num⟩
private def qAlo_265 : ℚ := (100483970712466036632101837485044504612437037746439837418145722772646302933805206884055880096592003305476168009291127968993023995038806259701119585690080175133143306383608034256112612066089447847 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qAhi_265 : ℚ := (50241985356233018316050918742522252306218518873219918709072861386323151466902603442027940048296001652738084004645563984496511997519820671699156214903047641457842354384638193190750314363480171777 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def qIlo_265 : ℚ := (100483970712466036632101837485044504612437037746439837418145722772646302933805206884055880096592003305476168009291127968993023995038806259701119585690080175133143306383608034256112612066089447847 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def qIhi_265 : ℚ := (50241985356233018316050918742522252306218518873219918709072861386323151466902603442027940048296001652738084004645563984496511997519820671699156214903047641457842354384638193190750314363480171777 / 1140610154405548804660292901425072831223307126812139982644798129474818791802169346626478202829342849944660577393398601827672176180343859499563165329930553547062998668590066237520718548061650944 : ℚ)
private def I_265 : RatInterval :=
  { lo := qIlo_265, hi := qIhi_265, h := by rw [Rat.le_iff]; norm_num [qIlo_265, qIhi_265] }
private theorem term_mem_265 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_265.mem (hessianTerm c x .t265) := by
  have hterm : hessianTerm c x .t265 =
      (c .t265 * 2) * ((x 2 ^ 8)) := by
    unfold hessianTerm derivativeCoeff monomial
    rw [show exponents .t265 = ![2, 0, 8] from rfl]
    norm_num [lowerExponent]
    try ring
    try simp
  rw [hterm]
  have hcI : I_265.mem (c .t265 * 2) := by
    constructor
    · have h := (hC .t265).1
      rw [show (coefficientInterval .t265).lo = qAlo_265 from rfl] at h
      norm_num [I_265, qIlo_265, qAlo_265] at h ⊢
      linarith
    · have h := (hC .t265).2
      rw [show (coefficientInterval .t265).hi = qAhi_265 from rfl] at h
      norm_num [I_265, qIhi_265, qAhi_265] at h ⊢
      linarith
  have hJmem : power_08.mem (x 2 ^ 8) := by
    simpa [powerTable, finitePower, power_08] using hP 2 8
  have hmain : termBound_265.mem ((c .t265 * 2) * ((x 2 ^ 8))) := by
    refine mem_mul_of_bounds hcI hJmem ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [I_265, power_08, termBound_265]
      rw [Rat.le_iff]
      norm_num [qIlo_265, qIhi_265]
  simpa using hmain

private def termBound_266 : RatInterval := ⟨(-162120792571162500486146395813609652587912651202963164739632931940131002957887020538876576522770595629216685744679751389810303196816724133756080354272422661256012281911 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ), (40530198142790625121536598953402413146978162800740791184908232985032750739471755134719144130692648907284435167712953376546415972013877045063354101764117344010569922877 / 1140610154405548804660292901425072831223307126812139982644798129474818791802169346626478202829342849944660577393398601827672176180343859499563165329930553547062998668590066237520718548061650944 : ℚ), by norm_num⟩
private def qAlo_266 : ℚ := (40530198142790625121536598953402413146978162800740791184908232985032750739471755134719144130692648907067690005045980828860961449726045427368845948806106395213589615073395357687186731221687340925 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def qAhi_266 : ℚ := (81060396285581250243073197906804826293956325601481582369816465970065501478943510269438288261385297814135380010091961657721922899452256543207600467473604819058088056810961514663740933135138380559 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qIlo_266 : ℚ := (40530198142790625121536598953402413146978162800740791184908232985032750739471755134719144130692648907067690005045980828860961449726045427368845948806106395213589615073395357687186731221687340925 / 1140610154405548804660292901425072831223307126812139982644798129474818791802169346626478202829342849944660577393398601827672176180343859499563165329930553547062998668590066237520718548061650944 : ℚ)
private def qIhi_266 : ℚ := (81060396285581250243073197906804826293956325601481582369816465970065501478943510269438288261385297814135380010091961657721922899452256543207600467473604819058088056810961514663740933135138380559 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def I_266 : RatInterval :=
  { lo := qIlo_266, hi := qIhi_266, h := by rw [Rat.le_iff]; norm_num [qIlo_266, qIhi_266] }
private theorem term_mem_266 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_266.mem (hessianTerm c x .t266) := by
  have hterm : hessianTerm c x .t266 =
      (c .t266 * 2) * ((x 2 ^ 9)) := by
    unfold hessianTerm derivativeCoeff monomial
    rw [show exponents .t266 = ![2, 0, 9] from rfl]
    norm_num [lowerExponent]
    try ring
    try simp
  rw [hterm]
  have hcI : I_266.mem (c .t266 * 2) := by
    constructor
    · have h := (hC .t266).1
      rw [show (coefficientInterval .t266).lo = qAlo_266 from rfl] at h
      norm_num [I_266, qIlo_266, qAlo_266] at h ⊢
      linarith
    · have h := (hC .t266).2
      rw [show (coefficientInterval .t266).hi = qAhi_266 from rfl] at h
      norm_num [I_266, qIhi_266, qAhi_266] at h ⊢
      linarith
  have hJmem : power_09.mem (x 2 ^ 9) := by
    simpa [powerTable, finitePower, power_09] using hP 2 9
  have hmain : termBound_266.mem ((c .t266 * 2) * ((x 2 ^ 9))) := by
    refine mem_mul_of_bounds hcI hJmem ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [I_266, power_09, termBound_266]
      rw [Rat.le_iff]
      norm_num [qIlo_266, qIhi_266]
  simpa using hmain

private def termBound_267 : RatInterval := ⟨(0 : ℚ), (47703276311225015137964933366179794156049429197847692003017349232799022226082773946848379200756277507345784342140201906301134960625406038178516857593992470741494431 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ), by norm_num⟩
private def qAlo_267 : ℚ := (23851638155612507568982466683089897078024714598923846001508674616399511113041386973424189600378138753518262076743937604873383802032853498064280460923001127764259811517684310237261408289268707159 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qAhi_267 : ℚ := (11925819077806253784491233341544948539012357299461923000754337308199755556520693486712094800189069376759131038371968802436691901016429691905870478015544594266768708453450018428286112106244234539 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def qIlo_267 : ℚ := (23851638155612507568982466683089897078024714598923846001508674616399511113041386973424189600378138753518262076743937604873383802032853498064280460923001127764259811517684310237261408289268707159 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def qIhi_267 : ℚ := (11925819077806253784491233341544948539012357299461923000754337308199755556520693486712094800189069376759131038371968802436691901016429691905870478015544594266768708453450018428286112106244234539 / 1140610154405548804660292901425072831223307126812139982644798129474818791802169346626478202829342849944660577393398601827672176180343859499563165329930553547062998668590066237520718548061650944 : ℚ)
private def I_267 : RatInterval :=
  { lo := qIlo_267, hi := qIhi_267, h := by rw [Rat.le_iff]; norm_num [qIlo_267, qIhi_267] }
private theorem term_mem_267 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_267.mem (hessianTerm c x .t267) := by
  have hterm : hessianTerm c x .t267 =
      (c .t267 * 2) * ((x 2 ^ 10)) := by
    unfold hessianTerm derivativeCoeff monomial
    rw [show exponents .t267 = ![2, 0, 10] from rfl]
    norm_num [lowerExponent]
    try ring
    try simp
  rw [hterm]
  have hcI : I_267.mem (c .t267 * 2) := by
    constructor
    · have h := (hC .t267).1
      rw [show (coefficientInterval .t267).lo = qAlo_267 from rfl] at h
      norm_num [I_267, qIlo_267, qAlo_267] at h ⊢
      linarith
    · have h := (hC .t267).2
      rw [show (coefficientInterval .t267).hi = qAhi_267 from rfl] at h
      norm_num [I_267, qIhi_267, qAhi_267] at h ⊢
      linarith
  have hJmem : power_10.mem (x 2 ^ 10) := by
    simpa [powerTable, finitePower, power_10] using hP 2 10
  have hmain : termBound_267.mem ((c .t267 * 2) * ((x 2 ^ 10))) := by
    refine mem_mul_of_bounds hcI hJmem ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [I_267, power_10, termBound_267]
      rw [Rat.le_iff]
      norm_num [qIlo_267, qIhi_267]
  simpa using hmain

private def termBound_268 : RatInterval := ⟨(-902503305846324519532251259258475427130267816251375253751632883884951806072834808845344618614606739571427994551426653745537186629343188611273964224428831761874507785618747464186611636748351 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ), (1805006611692649039064502518516950854260535632502750507503265767769903612145669617690689237229213479143734941012476151027752650174953431938022985598366051996284532151646899689759231513654695 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ), by norm_num⟩
private def qAlo_268 : ℚ := (-902503305846324519532251259258475427130267816251375253751632883884951806072834808845344618614606739571282377900010301413313129127803705917466010001948190186096219254637349470702120133248557889 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qAhi_268 : ℚ := (-902503305846324519532251259258475427130267816251375253751632883884951806072834808845344618614606739571282377900010301413313129123927215316162208287402985125209242156058921095580506784991862303 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qIlo_268 : ℚ := (-902503305846324519532251259258475427130267816251375253751632883884951806072834808845344618614606739571282377900010301413313129127803705917466010001948190186096219254637349470702120133248557889 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def qIhi_268 : ℚ := (-902503305846324519532251259258475427130267816251375253751632883884951806072834808845344618614606739571282377900010301413313129123927215316162208287402985125209242156058921095580506784991862303 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def I_268 : RatInterval :=
  { lo := qIlo_268, hi := qIhi_268, h := by rw [Rat.le_iff]; norm_num [qIlo_268, qIhi_268] }
private theorem term_mem_268 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_268.mem (hessianTerm c x .t268) := by
  have hterm : hessianTerm c x .t268 =
      (c .t268 * 2) * ((x 1 ^ 1)) := by
    unfold hessianTerm derivativeCoeff monomial
    rw [show exponents .t268 = ![2, 1, 0] from rfl]
    norm_num [lowerExponent]
    try ring
    try simp
  rw [hterm]
  have hcI : I_268.mem (c .t268 * 2) := by
    constructor
    · have h := (hC .t268).1
      rw [show (coefficientInterval .t268).lo = qAlo_268 from rfl] at h
      norm_num [I_268, qIlo_268, qAlo_268] at h ⊢
      linarith
    · have h := (hC .t268).2
      rw [show (coefficientInterval .t268).hi = qAhi_268 from rfl] at h
      norm_num [I_268, qIhi_268, qAhi_268] at h ⊢
      linarith
  have hJmem : power_01.mem (x 1 ^ 1) := by
    simpa [powerTable, finitePower, power_01] using hP 1 1
  have hmain : termBound_268.mem ((c .t268 * 2) * ((x 1 ^ 1))) := by
    refine mem_mul_of_bounds hcI hJmem ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [I_268, power_01, termBound_268]
      rw [Rat.le_iff]
      norm_num [qIlo_268, qIhi_268]
  simpa using hmain

private def termBound_269 : RatInterval := ⟨(-3299372948604068434856163177205916424816429580125156905359391189286556417798235843802757634903454511267194395267425264888829962574068187813423164648360556681600708108910393225986205654955 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ), (3299372948604068434856163177205916424816429580125156905359391189286556417798235843802757634903454511265587758408065494668380889437714554259299527899590306450629852743188778582412113427749 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ), by norm_num⟩
private def qAlo_269 : ℚ := (-824843237151017108714040794301479106204107395031289226339847797321639104449558960950689408725863627815729107600086812597957416935697571287443235299288548657825103331553651224739670726525998995 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def qAhi_269 : ℚ := (-1649686474302034217428081588602958212408214790062578452679695594643278208899117921901378817451727255631458215200173625195914833852715296138332219606334607315100515456796686332638320134214642931 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qIlo_269 : ℚ := (-824843237151017108714040794301479106204107395031289226339847797321639104449558960950689408725863627815729107600086812597957416935697571287443235299288548657825103331553651224739670726525998995 / 1140610154405548804660292901425072831223307126812139982644798129474818791802169346626478202829342849944660577393398601827672176180343859499563165329930553547062998668590066237520718548061650944 : ℚ)
private def qIhi_269 : ℚ := (-1649686474302034217428081588602958212408214790062578452679695594643278208899117921901378817451727255631458215200173625195914833852715296138332219606334607315100515456796686332638320134214642931 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def I_269 : RatInterval :=
  { lo := qIlo_269, hi := qIhi_269, h := by rw [Rat.le_iff]; norm_num [qIlo_269, qIhi_269] }
private def qJlo_269 : ℚ := (-20815864389328798163850480654728171077230524494533409610638224700807216119346720596024478883464648369701696733836591517926271803608380507562155537851606536282682339051026746635241705022884196081499961528860539382290409075545026174762699533280522874207663671674153009839347074170762293024306318452972106952305510671803832988458761923215369432124092008713025056482578798725283507155 / 20815864389328798163850480654728171077230524494533409610638224700807216119346720596024478883464648369684843227908562015582767132496646929816279813211354641525848259018778440691546366699323167100945918841095379622423387354295096957733925002768876520583464697770622321657076833170056511209332449663781837603694136444406281042053396870977465916057756101739472373801429441421111406337458176 : ℚ)
private def qJhi_269 : ℚ := (20815864389328798163850480654728171077230524494533409610638224700807216119346720596024478883464648369711833064438889668356001781171034650006996605567414206177429646641624501453496457342224969565253314794292797285483128218585919812326446356072081794795305200146873708019993172140955308372966390098239140469485242970579014495704884759282184418650686450197960785613488548084092544761 / 20815864389328798163850480654728171077230524494533409610638224700807216119346720596024478883464648369684843227908562015582767132496646929816279813211354641525848259018778440691546366699323167100945918841095379622423387354295096957733925002768876520583464697770622321657076833170056511209332449663781837603694136444406281042053396870977465916057756101739472373801429441421111406337458176 : ℚ)
private def J_269 : RatInterval :=
  { lo := qJlo_269, hi := qJhi_269, h := by rw [Rat.le_iff]; norm_num [qJlo_269, qJhi_269] }
private theorem term_mem_269 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_269.mem (hessianTerm c x .t269) := by
  have hterm : hessianTerm c x .t269 =
      (c .t269 * 2) * ((x 1 ^ 1) * (x 2 ^ 1)) := by
    unfold hessianTerm derivativeCoeff monomial
    rw [show exponents .t269 = ![2, 1, 1] from rfl]
    norm_num [lowerExponent]
    try ring
    try simp
  rw [hterm]
  have hcI : I_269.mem (c .t269 * 2) := by
    constructor
    · have h := (hC .t269).1
      rw [show (coefficientInterval .t269).lo = qAlo_269 from rfl] at h
      norm_num [I_269, qIlo_269, qAlo_269] at h ⊢
      linarith
    · have h := (hC .t269).2
      rw [show (coefficientInterval .t269).hi = qAhi_269 from rfl] at h
      norm_num [I_269, qIhi_269, qAhi_269] at h ⊢
      linarith
  have hJmem : J_269.mem ((x 1 ^ 1) * (x 2 ^ 1)) := by
    refine mem_mul_of_bounds (by simpa using hP 1 1) (by simpa using hP 2 1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [J_269, powerTable, finitePower, power_01, power_01]
      rw [Rat.le_iff]
      norm_num [qJlo_269, qJhi_269]
  have hmain : termBound_269.mem ((c .t269 * 2) * ((x 1 ^ 1) * (x 2 ^ 1))) := by
    refine mem_mul_of_bounds hcI hJmem ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [I_269, J_269, termBound_269]
      rw [Rat.le_iff]
      norm_num [qIlo_269, qIhi_269, qJlo_269, qJhi_269]
  simpa using hmain

private def termBound_270 : RatInterval := ⟨(-2820138833669922896838001261534530654684088068998433484784963481655466301894418897105933185598285590087555955702014468510037871804246344479825179874348207273179245791465552049791524941 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ), (2820138833669922896838001261534530654684088068998433484784963481655466301894418897105933185598285590088929228463010755737967455490043905367590239507566080112948047811855537906301709747 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ), by norm_num⟩
private def qAlo_270 : ℚ := (-176258677104370181052375078845908165917755504312402092799060217603466643868401181069120824099892849380215271445963084263313136207362316846614038965255734545694861582807850872496672506341247241 / 285152538601387201165073225356268207805826781703034995661199532368704697950542336656619550707335712486165144348349650456918044045085964874890791332482638386765749667147516559380179637015412736 : ℚ)
private def qAhi_270 : ℚ := (-2820138833669922896838001261534530654684088068998433484784963481655466301894418897105933185598285590083444343135409348213010179274740908981225017253393172172342733324779035619448160371854535617 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qIlo_270 : ℚ := (-176258677104370181052375078845908165917755504312402092799060217603466643868401181069120824099892849380215271445963084263313136207362316846614038965255734545694861582807850872496672506341247241 / 142576269300693600582536612678134103902913390851517497830599766184352348975271168328309775353667856243082572174174825228459022022542982437445395666241319193382874833573758279690089818507706368 : ℚ)
private def qIhi_270 : ℚ := (-2820138833669922896838001261534530654684088068998433484784963481655466301894418897105933185598285590083444343135409348213010179274740908981225017253393172172342733324779035619448160371854535617 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def I_270 : RatInterval :=
  { lo := qIlo_270, hi := qIhi_270, h := by rw [Rat.le_iff]; norm_num [qIlo_270, qIhi_270] }
private def qJlo_270 : ℚ := (-10407932194664399081925240327364085538615262247266704805319112350403608059673360298012239441732324184862663991352026747371309552754114255051177500872721994251610170226523765917235751331838997936374063183248019151484551263785623375668939344299083108078820560561822289096357543063301661797161664922611112005305492963355204366159009749373867802488246282581812517013941848061773783 / 10407932194664399081925240327364085538615262247266704805319112350403608059673360298012239441732324184842421613954281007791383566248323464908139906605677320762924129509389220345773183349661583550472959420547689811211693677147548478866962501384438260291732348885311160828538416585028255604666224831890918801847068222203140521026698435488732958028878050869736186900714720710555703168729088 : ℚ)
private def qJhi_270 : ℚ := (10407932194664399081925240327364085538615262247266704805319112350403608059673360298012239441732324184857595826050877672156444563972787183828756967014818159304236516431224888508108375172168611194497386550528604509934888170530296430426775004912263847823397649193344115112163929862991273915508855553100062473572991685121226359953647243172779944098903530022059027656274102601543965 / 10407932194664399081925240327364085538615262247266704805319112350403608059673360298012239441732324184842421613954281007791383566248323464908139906605677320762924129509389220345773183349661583550472959420547689811211693677147548478866962501384438260291732348885311160828538416585028255604666224831890918801847068222203140521026698435488732958028878050869736186900714720710555703168729088 : ℚ)
private def J_270 : RatInterval :=
  { lo := qJlo_270, hi := qJhi_270, h := by rw [Rat.le_iff]; norm_num [qJlo_270, qJhi_270] }
private theorem term_mem_270 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_270.mem (hessianTerm c x .t270) := by
  have hterm : hessianTerm c x .t270 =
      (c .t270 * 2) * ((x 1 ^ 1) * (x 2 ^ 2)) := by
    unfold hessianTerm derivativeCoeff monomial
    rw [show exponents .t270 = ![2, 1, 2] from rfl]
    norm_num [lowerExponent]
    try ring
    try simp
  rw [hterm]
  have hcI : I_270.mem (c .t270 * 2) := by
    constructor
    · have h := (hC .t270).1
      rw [show (coefficientInterval .t270).lo = qAlo_270 from rfl] at h
      norm_num [I_270, qIlo_270, qAlo_270] at h ⊢
      linarith
    · have h := (hC .t270).2
      rw [show (coefficientInterval .t270).hi = qAhi_270 from rfl] at h
      norm_num [I_270, qIhi_270, qAhi_270] at h ⊢
      linarith
  have hJmem : J_270.mem ((x 1 ^ 1) * (x 2 ^ 2)) := by
    refine mem_mul_of_bounds (by simpa using hP 1 1) (by simpa using hP 2 2) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [J_270, powerTable, finitePower, power_01, power_02]
      rw [Rat.le_iff]
      norm_num [qJlo_270, qJhi_270]
  have hmain : termBound_270.mem ((c .t270 * 2) * ((x 1 ^ 1) * (x 2 ^ 2))) := by
    refine mem_mul_of_bounds hcI hJmem ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [I_270, J_270, termBound_270]
      rw [Rat.le_iff]
      norm_num [qIlo_270, qIhi_270, qJlo_270, qJhi_270]
  simpa using hmain

private def termBound_271 : RatInterval := ⟨(-23260502653412395759915218865887494744431862527651078925437095781474179809304552915249143548774931355841376766194642956554281912457449288725444243585920554881569191905450007038344007 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ), (46521005306824791519830437731774989488863725055302157850874191562948359618609105830498287097549862711660100027306740173788196600753179398947694378908808904198877221176457913940885393 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ), by norm_num⟩
private def qAlo_271 : ℚ := (-5815125663353098939978804716471873686107965631912769731359273945368544952326138228812285887193732838945264415074168239724429964934678224161536501660622705930287518095773151165743451940366340777 / 1140610154405548804660292901425072831223307126812139982644798129474818791802169346626478202829342849944660577393398601827672176180343859499563165329930553547062998668590066237520718548061650944 : ℚ)
private def qAhi_271 : ℚ := (-5815125663353098939978804716471873686107965631912769731359273945368544952326138228812285887193732838945264415074168239724429964918744073688840377613093986352807454878734809409286276008859768393 / 1140610154405548804660292901425072831223307126812139982644798129474818791802169346626478202829342849944660577393398601827672176180343859499563165329930553547062998668590066237520718548061650944 : ℚ)
private def qIlo_271 : ℚ := (-5815125663353098939978804716471873686107965631912769731359273945368544952326138228812285887193732838945264415074168239724429964934678224161536501660622705930287518095773151165743451940366340777 / 570305077202774402330146450712536415611653563406069991322399064737409395901084673313239101414671424972330288696699300913836088090171929749781582664965276773531499334295033118760359274030825472 : ℚ)
private def qIhi_271 : ℚ := (-5815125663353098939978804716471873686107965631912769731359273945368544952326138228812285887193732838945264415074168239724429964918744073688840377613093986352807454878734809409286276008859768393 / 570305077202774402330146450712536415611653563406069991322399064737409395901084673313239101414671424972330288696699300913836088090171929749781582664965276773531499334295033118760359274030825472 : ℚ)
private def I_271 : RatInterval :=
  { lo := qIlo_271, hi := qIhi_271, h := by rw [Rat.le_iff]; norm_num [qIlo_271, qIhi_271] }
private def qJlo_271 : ℚ := (-20815864389328798163850480654728171077230524494533409610638224700807216119346720596024478883464648369728686570366919170699506452282768227752872330207666100934263726673872807397191795669278886977670072891834462797359845553056012978253624809330557221396390975307639453034831591926207142710222272554691301431845564116282578748662213724655236119451138043037772382984666855256633 / 20815864389328798163850480654728171077230524494533409610638224700807216119346720596024478883464648369684843227908562015582767132496646929816279813211354641525848259018778440691546366699323167100945918841095379622423387354295096957733925002768876520583464697770622321657076833170056511209332449663781837603694136444406281042053396870977465916057756101739472373801429441421111406337458176 : ℚ)
private def qJhi_271 : ℚ := (20815864389328798163850480654728171077230524494533409610638224700807216119346720596024478883464648369738822900969217321129236429845422370197713397923473770829011034264470562215446547985140461869880798260606647904507270739307777780130808291620618986839510642421370201878117733718866980241828400278503934510572407815656403790002890708991506997813132458168570337207174426894259 / 20815864389328798163850480654728171077230524494533409610638224700807216119346720596024478883464648369684843227908562015582767132496646929816279813211354641525848259018778440691546366699323167100945918841095379622423387354295096957733925002768876520583464697770622321657076833170056511209332449663781837603694136444406281042053396870977465916057756101739472373801429441421111406337458176 : ℚ)
private def J_271 : RatInterval :=
  { lo := qJlo_271, hi := qJhi_271, h := by rw [Rat.le_iff]; norm_num [qJlo_271, qJhi_271] }
private theorem term_mem_271 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_271.mem (hessianTerm c x .t271) := by
  have hterm : hessianTerm c x .t271 =
      (c .t271 * 2) * ((x 1 ^ 1) * (x 2 ^ 3)) := by
    unfold hessianTerm derivativeCoeff monomial
    rw [show exponents .t271 = ![2, 1, 3] from rfl]
    norm_num [lowerExponent]
    try ring
    try simp
  rw [hterm]
  have hcI : I_271.mem (c .t271 * 2) := by
    constructor
    · have h := (hC .t271).1
      rw [show (coefficientInterval .t271).lo = qAlo_271 from rfl] at h
      norm_num [I_271, qIlo_271, qAlo_271] at h ⊢
      linarith
    · have h := (hC .t271).2
      rw [show (coefficientInterval .t271).hi = qAhi_271 from rfl] at h
      norm_num [I_271, qIhi_271, qAhi_271] at h ⊢
      linarith
  have hJmem : J_271.mem ((x 1 ^ 1) * (x 2 ^ 3)) := by
    refine mem_mul_of_bounds (by simpa using hP 1 1) (by simpa using hP 2 3) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [J_271, powerTable, finitePower, power_01, power_03]
      rw [Rat.le_iff]
      norm_num [qJlo_271, qJhi_271]
  have hmain : termBound_271.mem ((c .t271 * 2) * ((x 1 ^ 1) * (x 2 ^ 3))) := by
    refine mem_mul_of_bounds hcI hJmem ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [I_271, J_271, termBound_271]
      rw [Rat.le_iff]
      norm_num [qIlo_271, qIhi_271, qJlo_271, qJhi_271]
  simpa using hmain

private def termBound_272 : RatInterval := ⟨(-33497811999462617500702081217928526733469436821593204642679252523846784279786036596862274500599562986219781128840834041474832435585028021336125148080430731645298559172290379242657 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ), (66995623998925235001404162435857053466938873643186409285358505047693568559572073193724549001199125972472185923029358374701386801589725985385737041068664805120194442986286178159313 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ), by norm_num⟩
private def qAlo_272 : ℚ := (-33497811999462617500702081217928526733469436821593204642679252523846784279786036596862274500599562986127509857171840915142786988075919935371701648643336948352304872550130068438786443445994830961 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qAhi_272 : ℚ := (-16748905999731308750351040608964263366734718410796602321339626261923392139893018298431137250299781493063754928585920457571393494004861643295341779050276094333784736600995350942028393010984910837 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def qIlo_272 : ℚ := (-33497811999462617500702081217928526733469436821593204642679252523846784279786036596862274500599562986127509857171840915142786988075919935371701648643336948352304872550130068438786443445994830961 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def qIhi_272 : ℚ := (-16748905999731308750351040608964263366734718410796602321339626261923392139893018298431137250299781493063754928585920457571393494004861643295341779050276094333784736600995350942028393010984910837 / 1140610154405548804660292901425072831223307126812139982644798129474818791802169346626478202829342849944660577393398601827672176180343859499563165329930553547062998668590066237520718548061650944 : ℚ)
private def I_272 : RatInterval :=
  { lo := qIlo_272, hi := qIhi_272, h := by rw [Rat.le_iff]; norm_num [qIlo_272, qIhi_272] }
private def qJlo_272 : ℚ := (-5203966097332199540962620163682042769307631123633352402659556175201804029836680149006119720866162092438079454808595286878963438545654057573267948525375888288700432018973398149105398383012842136549156172163027807529908619829575566526019576070822709249040819042170050591674009936930246424330677097998676103556462029906637947637982895827824494513616122234418077876984230729 / 5203966097332199540962620163682042769307631123633352402659556175201804029836680149006119720866162092421210806977140503895691783124161732454069953302838660381462064754694610172886591674830791775236479710273844905605846838573774239433481250692219130145866174442655580414269208292514127802333112415945459400923534111101570260513349217744366479014439025434868093450357360355277851584364544 : ℚ)
private def qJhi_272 : ℚ := (5203966097332199540962620163682042769307631123633352402659556175201804029836680149006119720866162092435545372158020749271530944154990521962057681596423970815013605121323959444541710303177648765610817855800034796801773551467031967444646478386373279159727216225813138705706639121561172248733547950400788386270660942486605625268049215429618537852741933954004657151241321795 / 5203966097332199540962620163682042769307631123633352402659556175201804029836680149006119720866162092421210806977140503895691783124161732454069953302838660381462064754694610172886591674830791775236479710273844905605846838573774239433481250692219130145866174442655580414269208292514127802333112415945459400923534111101570260513349217744366479014439025434868093450357360355277851584364544 : ℚ)
private def J_272 : RatInterval :=
  { lo := qJlo_272, hi := qJhi_272, h := by rw [Rat.le_iff]; norm_num [qJlo_272, qJhi_272] }
private theorem term_mem_272 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_272.mem (hessianTerm c x .t272) := by
  have hterm : hessianTerm c x .t272 =
      (c .t272 * 2) * ((x 1 ^ 1) * (x 2 ^ 4)) := by
    unfold hessianTerm derivativeCoeff monomial
    rw [show exponents .t272 = ![2, 1, 4] from rfl]
    norm_num [lowerExponent]
    try ring
    try simp
  rw [hterm]
  have hcI : I_272.mem (c .t272 * 2) := by
    constructor
    · have h := (hC .t272).1
      rw [show (coefficientInterval .t272).lo = qAlo_272 from rfl] at h
      norm_num [I_272, qIlo_272, qAlo_272] at h ⊢
      linarith
    · have h := (hC .t272).2
      rw [show (coefficientInterval .t272).hi = qAhi_272 from rfl] at h
      norm_num [I_272, qIhi_272, qAhi_272] at h ⊢
      linarith
  have hJmem : J_272.mem ((x 1 ^ 1) * (x 2 ^ 4)) := by
    refine mem_mul_of_bounds (by simpa using hP 1 1) (by simpa using hP 2 4) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [J_272, powerTable, finitePower, power_01, power_04]
      rw [Rat.le_iff]
      norm_num [qJlo_272, qJhi_272]
  have hmain : termBound_272.mem ((c .t272 * 2) * ((x 1 ^ 1) * (x 2 ^ 4))) := by
    refine mem_mul_of_bounds hcI hJmem ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [I_272, J_272, termBound_272]
      rw [Rat.le_iff]
      norm_num [qIlo_272, qIhi_272, qJlo_272, qJhi_272]
  simpa using hmain

private def termBound_273 : RatInterval := ⟨(-75425023706248929001325687554479043045205771908841887163596792923952359634705474157511543914572031727131077468365603890549381603140306223984284482574114336829055674003723327801 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ), (18856255926562232250331421888619760761301442977210471790899198230988089908676368539377885978643007931791951462075223148625152622359948366983123742551179667527550856215799752037 / 1140610154405548804660292901425072831223307126812139982644798129474818791802169346626478202829342849944660577393398601827672176180343859499563165329930553547062998668590066237520718548061650944 : ℚ), by norm_num⟩
private def qAlo_273 : ℚ := (4714063981640558062582855472154940190325360744302617947724799557747022477169092134844471494660751982929651108436086334283518280987198996939688389779475034852541358802276088395871902739089585799 / 570305077202774402330146450712536415611653563406069991322399064737409395901084673313239101414671424972330288696699300913836088090171929749781582664965276773531499334295033118760359274030825472 : ℚ)
private def qAhi_273 : ℚ := (37712511853124464500662843777239521522602885954420943581798396461976179817352737078755771957286015863437208867488690674268146247945225792931482379787897411486714315987775808909014992846179992823 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qIlo_273 : ℚ := (4714063981640558062582855472154940190325360744302617947724799557747022477169092134844471494660751982929651108436086334283518280987198996939688389779475034852541358802276088395871902739089585799 / 285152538601387201165073225356268207805826781703034995661199532368704697950542336656619550707335712486165144348349650456918044045085964874890791332482638386765749667147516559380179637015412736 : ℚ)
private def qIhi_273 : ℚ := (37712511853124464500662843777239521522602885954420943581798396461976179817352737078755771957286015863437208867488690674268146247945225792931482379787897411486714315987775808909014992846179992823 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def I_273 : RatInterval :=
  { lo := qIlo_273, hi := qIhi_273, h := by rw [Rat.le_iff]; norm_num [qIlo_273, qIhi_273] }
private def qJlo_273 : ℚ := (-20815864389328798163850480654728171077230524494533409610638224700807216119346720596024478883464648369755676406897246823472741100957155947943589122563725665585845114296718868159143787772420641882272500871692478560469459670133034671423639613906371423197241246365507940173515756538205154042867059589697620438060707484547599291373058703041476637752428030474292048347293323 / 20815864389328798163850480654728171077230524494533409610638224700807216119346720596024478883464648369684843227908562015582767132496646929816279813211354641525848259018778440691546366699323167100945918841095379622423387354295096957733925002768876520583464697770622321657076833170056511209332449663781837603694136444406281042053396870977465916057756101739472373801429441421111406337458176 : ℚ)
private def qJhi_273 : ℚ := (20815864389328798163850480654728171077230524494533409610638224700807216119346720596024478883464648369765812737499544973902471078519810090388430190279533335480592421887316622977396700722097459915992050177567139172368088851739188187370570372416072024259600066356159284243268054781557440352286606040932950808000727800925602754588978515248376476505119248721239488427492075 / 20815864389328798163850480654728171077230524494533409610638224700807216119346720596024478883464648369684843227908562015582767132496646929816279813211354641525848259018778440691546366699323167100945918841095379622423387354295096957733925002768876520583464697770622321657076833170056511209332449663781837603694136444406281042053396870977465916057756101739472373801429441421111406337458176 : ℚ)
private def J_273 : RatInterval :=
  { lo := qJlo_273, hi := qJhi_273, h := by rw [Rat.le_iff]; norm_num [qJlo_273, qJhi_273] }
private theorem term_mem_273 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_273.mem (hessianTerm c x .t273) := by
  have hterm : hessianTerm c x .t273 =
      (c .t273 * 2) * ((x 1 ^ 1) * (x 2 ^ 5)) := by
    unfold hessianTerm derivativeCoeff monomial
    rw [show exponents .t273 = ![2, 1, 5] from rfl]
    norm_num [lowerExponent]
    try ring
    try simp
  rw [hterm]
  have hcI : I_273.mem (c .t273 * 2) := by
    constructor
    · have h := (hC .t273).1
      rw [show (coefficientInterval .t273).lo = qAlo_273 from rfl] at h
      norm_num [I_273, qIlo_273, qAlo_273] at h ⊢
      linarith
    · have h := (hC .t273).2
      rw [show (coefficientInterval .t273).hi = qAhi_273 from rfl] at h
      norm_num [I_273, qIhi_273, qAhi_273] at h ⊢
      linarith
  have hJmem : J_273.mem ((x 1 ^ 1) * (x 2 ^ 5)) := by
    refine mem_mul_of_bounds (by simpa using hP 1 1) (by simpa using hP 2 5) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [J_273, powerTable, finitePower, power_01, power_05]
      rw [Rat.le_iff]
      norm_num [qJlo_273, qJhi_273]
  have hmain : termBound_273.mem ((c .t273 * 2) * ((x 1 ^ 1) * (x 2 ^ 5))) := by
    refine mem_mul_of_bounds hcI hJmem ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [I_273, J_273, termBound_273]
      rw [Rat.le_iff]
      norm_num [qIlo_273, qIhi_273, qJlo_273, qJhi_273]
  simpa using hmain

private def termBound_274 : RatInterval := ⟨(-207622325684500384513865244116888347289974701892155113239418525792115762043912025067526138845219301717837184392122019528199337113577491546007779451324592370502330613383443655 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ), (207622325684500384513865244116888347289974701892155113239418525792115762043912025067526138845219301717736082247421509472877312263446093833313338665145044620112027942027226275 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ), by norm_num⟩
private def qAlo_274 : ℚ := (103811162842250192256932622058444173644987350946077556619709262896057881021956012533763069422609650858447486989015093965539038669646324160363857471831351774245398736256995613657969513714149985531 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qAhi_274 : ℚ := (103811162842250192256932622058444173644987350946077556619709262896057881021956012533763069422609650858447486989015093965539038669670036602020996529920771697181053841747355299585449176999624719799 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qIlo_274 : ℚ := (103811162842250192256932622058444173644987350946077556619709262896057881021956012533763069422609650858447486989015093965539038669646324160363857471831351774245398736256995613657969513714149985531 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def qIhi_274 : ℚ := (103811162842250192256932622058444173644987350946077556619709262896057881021956012533763069422609650858447486989015093965539038669670036602020996529920771697181053841747355299585449176999624719799 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def I_274 : RatInterval :=
  { lo := qIlo_274, hi := qIhi_274, h := by rw [Rat.le_iff]; norm_num [qIlo_274, qIhi_274] }
private def qJlo_274 : ℚ := (-20815864389328798163850480654728171077230524494533409610638224700807216119346720596024478883464648369779307655764708800289088402857003950483788586457563117806383115698739653362051708266455379550115573601462216886787725181880501600484738274555764187487536524113393426867224415508840429015837141885299202405582130752840436617013846928192770272430247017394724881902435 / 20815864389328798163850480654728171077230524494533409610638224700807216119346720596024478883464648369684843227908562015582767132496646929816279813211354641525848259018778440691546366699323167100945918841095379622423387354295096957733925002768876520583464697770622321657076833170056511209332449663781837603694136444406281042053396870977465916057756101739472373801429441421111406337458176 : ℚ)
private def qJhi_274 : ℚ := (20815864389328798163850480654728171077230524494533409610638224700807216119346720596024478883464648369769171325162410649859358425294349808038947518741755447911635808108141898543796955947114606066362220335997102084061970821490806698318082171853807267283873524319494479747872675384716615719861144122245200973429681963447683715260703985135353879727310181352921942059425 / 20815864389328798163850480654728171077230524494533409610638224700807216119346720596024478883464648369684843227908562015582767132496646929816279813211354641525848259018778440691546366699323167100945918841095379622423387354295096957733925002768876520583464697770622321657076833170056511209332449663781837603694136444406281042053396870977465916057756101739472373801429441421111406337458176 : ℚ)
private def J_274 : RatInterval :=
  { lo := qJlo_274, hi := qJhi_274, h := by rw [Rat.le_iff]; norm_num [qJlo_274, qJhi_274] }
private theorem term_mem_274 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_274.mem (hessianTerm c x .t274) := by
  have hterm : hessianTerm c x .t274 =
      (c .t274 * 2) * ((x 1 ^ 1) * (x 2 ^ 6)) := by
    unfold hessianTerm derivativeCoeff monomial
    rw [show exponents .t274 = ![2, 1, 6] from rfl]
    norm_num [lowerExponent]
    try ring
    try simp
  rw [hterm]
  have hcI : I_274.mem (c .t274 * 2) := by
    constructor
    · have h := (hC .t274).1
      rw [show (coefficientInterval .t274).lo = qAlo_274 from rfl] at h
      norm_num [I_274, qIlo_274, qAlo_274] at h ⊢
      linarith
    · have h := (hC .t274).2
      rw [show (coefficientInterval .t274).hi = qAhi_274 from rfl] at h
      norm_num [I_274, qIhi_274, qAhi_274] at h ⊢
      linarith
  have hJmem : J_274.mem ((x 1 ^ 1) * (x 2 ^ 6)) := by
    refine mem_mul_of_bounds (by simpa using hP 1 1) (by simpa using hP 2 6) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [J_274, powerTable, finitePower, power_01, power_06]
      rw [Rat.le_iff]
      norm_num [qJlo_274, qJhi_274]
  have hmain : termBound_274.mem ((c .t274 * 2) * ((x 1 ^ 1) * (x 2 ^ 6))) := by
    refine mem_mul_of_bounds hcI hJmem ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [I_274, J_274, termBound_274]
      rw [Rat.le_iff]
      norm_num [qIlo_274, qIhi_274, qJlo_274, qJhi_274]
  simpa using hmain

private def termBound_275 : RatInterval := ⟨(-6210927175772236630235693475676065868052346689611138050394499818970378517920430253599388440580835496013746255623069623653616639206708712869703257682347413335166181344045 / 570305077202774402330146450712536415611653563406069991322399064737409395901084673313239101414671424972330288696699300913836088090171929749781582664965276773531499334295033118760359274030825472 : ℚ), (3105463587886118315117846737838032934026173344805569025197249909485189258960215126799694220290417748008385340084417882455131514028848433521265757730736690480309419546373 / 285152538601387201165073225356268207805826781703034995661199532368704697950542336656619550707335712486165144348349650456918044045085964874890791332482638386765749667147516559380179637015412736 : ℚ), by norm_num⟩
private def qAlo_275 : ℚ := (24843708703088946520942773902704263472209386758444552201577999275881514071681721014397553762323341983938233373050424167213104876362858309842171858561027447122862433910552064018218294559328367509 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qAhi_275 : ℚ := (24843708703088946520942773902704263472209386758444552201577999275881514071681721014397553762323341983938233373050424167213104876370243990246563132764935526867801011855942732356983050339332375657 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qIlo_275 : ℚ := (24843708703088946520942773902704263472209386758444552201577999275881514071681721014397553762323341983938233373050424167213104876362858309842171858561027447122862433910552064018218294559328367509 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def qIhi_275 : ℚ := (24843708703088946520942773902704263472209386758444552201577999275881514071681721014397553762323341983938233373050424167213104876370243990246563132764935526867801011855942732356983050339332375657 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def I_275 : RatInterval :=
  { lo := qIlo_275, hi := qIhi_275, h := by rw [Rat.le_iff]; norm_num [qIlo_275, qIhi_275] }
private def qJlo_275 : ℚ := (-10407932194664399081925240327364085538615262247266704805319112350403608059673360298012239441732324184891333121713787238122987874815771834067152957459892615118713250959782465468362131176661153032931727649505671176725929143148613650603867392162433278334087146526332347104021902783844104009339842370562996711632557529124059223145151133722505982058883131815085267095 / 10407932194664399081925240327364085538615262247266704805319112350403608059673360298012239441732324184842421613954281007791383566248323464908139906605677320762924129509389220345773183349661583550472959420547689811211693677147548478866962501384438260291732348885311160828538416585028255604666224831890918801847068222203140521026698435488732958028878050869736186900714720710555703168729088 : ℚ)
private def qJhi_275 : ℚ := (10407932194664399081925240327364085538615262247266704805319112350403608059673360298012239441732324184896401287014936313337852863597098905289573491317796450066086904755081342877489507336331539774808404282241514268042109845078341228147486371504451538397520793555399645557568337550982163527495096838485276945254172664751010010884026811761972184138605986053227595589 / 10407932194664399081925240327364085538615262247266704805319112350403608059673360298012239441732324184842421613954281007791383566248323464908139906605677320762924129509389220345773183349661583550472959420547689811211693677147548478866962501384438260291732348885311160828538416585028255604666224831890918801847068222203140521026698435488732958028878050869736186900714720710555703168729088 : ℚ)
private def J_275 : RatInterval :=
  { lo := qJlo_275, hi := qJhi_275, h := by rw [Rat.le_iff]; norm_num [qJlo_275, qJhi_275] }
private theorem term_mem_275 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_275.mem (hessianTerm c x .t275) := by
  have hterm : hessianTerm c x .t275 =
      (c .t275 * 2) * ((x 1 ^ 1) * (x 2 ^ 7)) := by
    unfold hessianTerm derivativeCoeff monomial
    rw [show exponents .t275 = ![2, 1, 7] from rfl]
    norm_num [lowerExponent]
    try ring
    try simp
  rw [hterm]
  have hcI : I_275.mem (c .t275 * 2) := by
    constructor
    · have h := (hC .t275).1
      rw [show (coefficientInterval .t275).lo = qAlo_275 from rfl] at h
      norm_num [I_275, qIlo_275, qAlo_275] at h ⊢
      linarith
    · have h := (hC .t275).2
      rw [show (coefficientInterval .t275).hi = qAhi_275 from rfl] at h
      norm_num [I_275, qIhi_275, qAhi_275] at h ⊢
      linarith
  have hJmem : J_275.mem ((x 1 ^ 1) * (x 2 ^ 7)) := by
    refine mem_mul_of_bounds (by simpa using hP 1 1) (by simpa using hP 2 7) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [J_275, powerTable, finitePower, power_01, power_07]
      rw [Rat.le_iff]
      norm_num [qJlo_275, qJhi_275]
  have hmain : termBound_275.mem ((c .t275 * 2) * ((x 1 ^ 1) * (x 2 ^ 7))) := by
    refine mem_mul_of_bounds hcI hJmem ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [I_275, J_275, termBound_275]
      rw [Rat.le_iff]
      norm_num [qIlo_275, qIhi_275, qJlo_275, qJhi_275]
  simpa using hmain

private def termBound_276 : RatInterval := ⟨(-66464100875791678325816918483711643073993848645599191848498114453563672848505472840930302002694843400206931926951129961003246657324055600079503190458849534045574549931 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ), (33232050437895839162908459241855821536996924322799595924249057226781836424252736420465151001347421700119648382976887496313658529667303596304717456838379476885472530077 / 1140610154405548804660292901425072831223307126812139982644798129474818791802169346626478202829342849944660577393398601827672176180343859499563165329930553547062998668590066237520718548061650944 : ℚ), by norm_num⟩
private def qAlo_276 : ℚ := (-4154006304736979895363557405231977692124615540349949490531132153347729553031592052558143875168427712490718679172819798783558446382442346761125693151786894706779516802424924114321379431635892465 / 285152538601387201165073225356268207805826781703034995661199532368704697950542336656619550707335712486165144348349650456918044045085964874890791332482638386765749667147516559380179637015412736 : ℚ)
private def qAhi_276 : ℚ := (-66464100875791678325816918483711643073993848645599191848498114453563672848505472840930302002694843399851498866765116780536935142117689142438198620681156621733839354057638839267068213696164892617 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qIlo_276 : ℚ := (-4154006304736979895363557405231977692124615540349949490531132153347729553031592052558143875168427712490718679172819798783558446382442346761125693151786894706779516802424924114321379431635892465 / 142576269300693600582536612678134103902913390851517497830599766184352348975271168328309775353667856243082572174174825228459022022542982437445395666241319193382874833573758279690089818507706368 : ℚ)
private def qIhi_276 : ℚ := (-66464100875791678325816918483711643073993848645599191848498114453563672848505472840930302002694843399851498866765116780536935142117689142438198620681156621733839354057638839267068213696164892617 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def I_276 : RatInterval :=
  { lo := qIlo_276, hi := qIhi_276, h := by rw [Rat.le_iff]; norm_num [qIlo_276, qIhi_276] }
private def qJlo_276 : ℚ := (-20815864389328798163850480654728171077230524494533409610638224700807216119346720596024478883464648369806297492295036453062323051531391670674505378813622682457964503321588303295196875079014589916567407398072894562051348841217928441273736709260909910839901697895789747758736186057493781650102973945450385338813758533708311615169981962713855648679813133009229895 / 20815864389328798163850480654728171077230524494533409610638224700807216119346720596024478883464648369684843227908562015582767132496646929816279813211354641525848259018778440691546366699323167100945918841095379622423387354295096957733925002768876520583464697770622321657076833170056511209332449663781837603694136444406281042053396870977465916057756101739472373801429441421111406337458176 : ℚ)
private def qJhi_276 : ℚ := (20815864389328798163850480654728171077230524494533409610638224700807216119346720596024478883464648369796161161692738302632593073968737528229664311097815012563217195730990548476942122759673816432814054132594636999512380393888713033265916894594793790789830109573419501063900928269949232230133556274578199443312345394996497591941202431038191547455112493744927725 / 20815864389328798163850480654728171077230524494533409610638224700807216119346720596024478883464648369684843227908562015582767132496646929816279813211354641525848259018778440691546366699323167100945918841095379622423387354295096957733925002768876520583464697770622321657076833170056511209332449663781837603694136444406281042053396870977465916057756101739472373801429441421111406337458176 : ℚ)
private def J_276 : RatInterval :=
  { lo := qJlo_276, hi := qJhi_276, h := by rw [Rat.le_iff]; norm_num [qJlo_276, qJhi_276] }
private theorem term_mem_276 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_276.mem (hessianTerm c x .t276) := by
  have hterm : hessianTerm c x .t276 =
      (c .t276 * 2) * ((x 1 ^ 1) * (x 2 ^ 8)) := by
    unfold hessianTerm derivativeCoeff monomial
    rw [show exponents .t276 = ![2, 1, 8] from rfl]
    norm_num [lowerExponent]
    try ring
    try simp
  rw [hterm]
  have hcI : I_276.mem (c .t276 * 2) := by
    constructor
    · have h := (hC .t276).1
      rw [show (coefficientInterval .t276).lo = qAlo_276 from rfl] at h
      norm_num [I_276, qIlo_276, qAlo_276] at h ⊢
      linarith
    · have h := (hC .t276).2
      rw [show (coefficientInterval .t276).hi = qAhi_276 from rfl] at h
      norm_num [I_276, qIhi_276, qAhi_276] at h ⊢
      linarith
  have hJmem : J_276.mem ((x 1 ^ 1) * (x 2 ^ 8)) := by
    refine mem_mul_of_bounds (by simpa using hP 1 1) (by simpa using hP 2 8) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [J_276, powerTable, finitePower, power_01, power_08]
      rw [Rat.le_iff]
      norm_num [qJlo_276, qJhi_276]
  have hmain : termBound_276.mem ((c .t276 * 2) * ((x 1 ^ 1) * (x 2 ^ 8))) := by
    refine mem_mul_of_bounds hcI hJmem ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [I_276, J_276, termBound_276]
      rw [Rat.le_iff]
      norm_num [qIlo_276, qIhi_276, qJlo_276, qJhi_276]
  simpa using hmain

private def termBound_277 : RatInterval := ⟨(-75278296142311958891694991061177590516542519261563008376220537839598746663269140474654162015211164123001232272134282469198259927613076133545009723862695612894298891 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ), (9409787017788994861461873882647198814567814907695376047027567229949843332908642559331770251901395515370571917688317146298865262469172307020809908632504645790766097 / 570305077202774402330146450712536415611653563406069991322399064737409395901084673313239101414671424972330288696699300913836088090171929749781582664965276773531499334295033118760359274030825472 : ℚ), by norm_num⟩
private def qAlo_277 : ℚ := (-37639148071155979445847495530588795258271259630781504188110268919799373331634570237327081007605582061256601658796122210233396586114658353189318182752126626633874577429594783355487365889049471165 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qAhi_277 : ℚ := (-18819574035577989722923747765294397629135629815390752094055134459899686665817285118663540503802791030628300829398061105116698293057304369742379775182054362775857769991021576929520241680705277201 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def qIlo_277 : ℚ := (-37639148071155979445847495530588795258271259630781504188110268919799373331634570237327081007605582061256601658796122210233396586114658353189318182752126626633874577429594783355487365889049471165 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def qIhi_277 : ℚ := (-18819574035577989722923747765294397629135629815390752094055134459899686665817285118663540503802791030628300829398061105116698293057304369742379775182054362775857769991021576929520241680705277201 / 1140610154405548804660292901425072831223307126812139982644798129474818791802169346626478202829342849944660577393398601827672176180343859499563165329930553547062998668590066237520718548061650944 : ℚ)
private def I_277 : RatInterval :=
  { lo := qIlo_277, hi := qIhi_277, h := by rw [Rat.le_iff]; norm_num [qIlo_277, qIhi_277] }
private def qJlo_277 : ℚ := (-2601983048666099770481310081841021384653815561816676201329778087600902014918340074503059860433081046226207009994737766127401299788241423540627838409480599361125986193355309066454195915466585390886757374814874500077772487606346167109286949954278236944854413868432247484064925599942808979591073998631981216398948546619898985753603628883995043942273105669805 / 2601983048666099770481310081841021384653815561816676201329778087600902014918340074503059860433081046210605403488570251947845891562080866227034976651419330190731032377347305086443295837415395887618239855136922452802923419286887119716740625346109565072933087221327790207134604146257063901166556207972729700461767055550785130256674608872183239507219512717434046725178680177638925792182272 : ℚ)
private def qJhi_277 : ℚ := (2601983048666099770481310081841021384653815561816676201329778087600902014918340074503059860433081046227474051320025034931117546983573191346232971873956558097969399642180028418736039955384182076355926533000478117883469423956218124725337158785302701941513899191757984544656556307442822826805905043855750380929649848289329750332213761767996642646939554605191 / 2601983048666099770481310081841021384653815561816676201329778087600902014918340074503059860433081046210605403488570251947845891562080866227034976651419330190731032377347305086443295837415395887618239855136922452802923419286887119716740625346109565072933087221327790207134604146257063901166556207972729700461767055550785130256674608872183239507219512717434046725178680177638925792182272 : ℚ)
private def J_277 : RatInterval :=
  { lo := qJlo_277, hi := qJhi_277, h := by rw [Rat.le_iff]; norm_num [qJlo_277, qJhi_277] }
private theorem term_mem_277 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_277.mem (hessianTerm c x .t277) := by
  have hterm : hessianTerm c x .t277 =
      (c .t277 * 2) * ((x 1 ^ 1) * (x 2 ^ 9)) := by
    unfold hessianTerm derivativeCoeff monomial
    rw [show exponents .t277 = ![2, 1, 9] from rfl]
    norm_num [lowerExponent]
    try ring
    try simp
  rw [hterm]
  have hcI : I_277.mem (c .t277 * 2) := by
    constructor
    · have h := (hC .t277).1
      rw [show (coefficientInterval .t277).lo = qAlo_277 from rfl] at h
      norm_num [I_277, qIlo_277, qAlo_277] at h ⊢
      linarith
    · have h := (hC .t277).2
      rw [show (coefficientInterval .t277).hi = qAhi_277 from rfl] at h
      norm_num [I_277, qIhi_277, qAhi_277] at h ⊢
      linarith
  have hJmem : J_277.mem ((x 1 ^ 1) * (x 2 ^ 9)) := by
    refine mem_mul_of_bounds (by simpa using hP 1 1) (by simpa using hP 2 9) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [J_277, powerTable, finitePower, power_01, power_09]
      rw [Rat.le_iff]
      norm_num [qJlo_277, qJhi_277]
  have hmain : termBound_277.mem ((c .t277 * 2) * ((x 1 ^ 1) * (x 2 ^ 9))) := by
    refine mem_mul_of_bounds hcI hJmem ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [I_277, J_277, termBound_277]
      rw [Rat.le_iff]
      norm_num [qIlo_277, qIhi_277, qJlo_277, qJhi_277]
  simpa using hmain

private def termBound_278 : RatInterval := ⟨(0 : ℚ), (2689127958709560692300078324145224000707519544656922777770396225458126079132277528461670838933012152046869244628378964851000367751775413814044843773388241862388646396506975966116664499553 / 1140610154405548804660292901425072831223307126812139982644798129474818791802169346626478202829342849944660577393398601827672176180343859499563165329930553547062998668590066237520718548061650944 : ℚ), by norm_num⟩
private def qAlo_278 : ℚ := (5378255917419121384600156648290448001415039089313845555540792450916252158264555056923341677866024304086765046054282778776265903312991162935857689284062905698715453607710645983143828119019562351 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qAhi_278 : ℚ := (5378255917419121384600156648290448001415039089313845555540792450916252158264555056923341677866024304086765046054282778776265903321362753016280483983279754898246252292304792455274898427320932637 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qIlo_278 : ℚ := (5378255917419121384600156648290448001415039089313845555540792450916252158264555056923341677866024304086765046054282778776265903312991162935857689284062905698715453607710645983143828119019562351 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def qIhi_278 : ℚ := (5378255917419121384600156648290448001415039089313845555540792450916252158264555056923341677866024304086765046054282778776265903321362753016280483983279754898246252292304792455274898427320932637 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def I_278 : RatInterval :=
  { lo := qIlo_278, hi := qIhi_278, h := by rw [Rat.le_iff]; norm_num [qIlo_278, qIhi_278] }
private theorem term_mem_278 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_278.mem (hessianTerm c x .t278) := by
  have hterm : hessianTerm c x .t278 =
      (c .t278 * 2) * ((x 1 ^ 2)) := by
    unfold hessianTerm derivativeCoeff monomial
    rw [show exponents .t278 = ![2, 2, 0] from rfl]
    norm_num [lowerExponent]
    try ring
    try simp
  rw [hterm]
  have hcI : I_278.mem (c .t278 * 2) := by
    constructor
    · have h := (hC .t278).1
      rw [show (coefficientInterval .t278).lo = qAlo_278 from rfl] at h
      norm_num [I_278, qIlo_278, qAlo_278] at h ⊢
      linarith
    · have h := (hC .t278).2
      rw [show (coefficientInterval .t278).hi = qAhi_278 from rfl] at h
      norm_num [I_278, qIhi_278, qAhi_278] at h ⊢
      linarith
  have hJmem : power_02.mem (x 1 ^ 2) := by
    simpa [powerTable, finitePower, power_02] using hP 1 2
  have hmain : termBound_278.mem ((c .t278 * 2) * ((x 1 ^ 2))) := by
    refine mem_mul_of_bounds hcI hJmem ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [I_278, power_02, termBound_278]
      rw [Rat.le_iff]
      norm_num [qIlo_278, qIhi_278]
  simpa using hmain

private def termBound_279 : RatInterval := ⟨(-2820138833669922896838001261534530654684088068998433484784963481655466301894418897105933185598285590087555955702014468510037871804246344479825179874367012151338242857844607479841664647 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ), (5640277667339845793676002523069061309368176137996866969569926963310932603788837794211866371196571180177858456926021511475934910980087810735180479015169769982214089756469186672703698907 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ), by norm_num⟩
private def qAlo_279 : ℚ := (-2820138833669922896838001261534530654684088068998433484784963481655466301894418897105933185598285590083444343135409348213010179317797069545824623444110557609276782391304669389996899807776837591 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qAhi_279 : ℚ := (-2820138833669922896838001261534530654684088068998433484784963481655466301894418897105933185598285590083444343135409348213010179274740908981225017253374367294183736258399980189398020665537653883 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qIlo_279 : ℚ := (-2820138833669922896838001261534530654684088068998433484784963481655466301894418897105933185598285590083444343135409348213010179317797069545824623444110557609276782391304669389996899807776837591 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def qIhi_279 : ℚ := (-2820138833669922896838001261534530654684088068998433484784963481655466301894418897105933185598285590083444343135409348213010179274740908981225017253374367294183736258399980189398020665537653883 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def I_279 : RatInterval :=
  { lo := qIlo_279, hi := qIhi_279, h := by rw [Rat.le_iff]; norm_num [qIlo_279, qIhi_279] }
private def qJlo_279 : ℚ := (-10407932194664399081925240327364085538615262247266704805319112350403608059673360298012239441732324184862663991352026747371309552754114255051177500872721994251610170226523765917235751331838997936374063183248019151484551263785623375668939344299083108078820560561822289096357543063301661797161664922611112005305492963355204366159009749373867802488246282581812517013941848061773783 / 10407932194664399081925240327364085538615262247266704805319112350403608059673360298012239441732324184842421613954281007791383566248323464908139906605677320762924129509389220345773183349661583550472959420547689811211693677147548478866962501384438260291732348885311160828538416585028255604666224831890918801847068222203140521026698435488732958028878050869736186900714720710555703168729088 : ℚ)
private def qJhi_279 : ℚ := (10407932194664399081925240327364085538615262247266704805319112350403608059673360298012239441732324184857595826050877672156444563972787183828756967014818159304236516431224888508108375172168611194497386550528604509934888170530296430426775004912263847823397649193344115112163929862991273915508855553100062473572991685121226359953647243172779944098903530022059027656274102601543965 / 10407932194664399081925240327364085538615262247266704805319112350403608059673360298012239441732324184842421613954281007791383566248323464908139906605677320762924129509389220345773183349661583550472959420547689811211693677147548478866962501384438260291732348885311160828538416585028255604666224831890918801847068222203140521026698435488732958028878050869736186900714720710555703168729088 : ℚ)
private def J_279 : RatInterval :=
  { lo := qJlo_279, hi := qJhi_279, h := by rw [Rat.le_iff]; norm_num [qJlo_279, qJhi_279] }
private theorem term_mem_279 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_279.mem (hessianTerm c x .t279) := by
  have hterm : hessianTerm c x .t279 =
      (c .t279 * 2) * ((x 1 ^ 2) * (x 2 ^ 1)) := by
    unfold hessianTerm derivativeCoeff monomial
    rw [show exponents .t279 = ![2, 2, 1] from rfl]
    norm_num [lowerExponent]
    try ring
    try simp
  rw [hterm]
  have hcI : I_279.mem (c .t279 * 2) := by
    constructor
    · have h := (hC .t279).1
      rw [show (coefficientInterval .t279).lo = qAlo_279 from rfl] at h
      norm_num [I_279, qIlo_279, qAlo_279] at h ⊢
      linarith
    · have h := (hC .t279).2
      rw [show (coefficientInterval .t279).hi = qAhi_279 from rfl] at h
      norm_num [I_279, qIhi_279, qAhi_279] at h ⊢
      linarith
  have hJmem : J_279.mem ((x 1 ^ 2) * (x 2 ^ 1)) := by
    refine mem_mul_of_bounds (by simpa using hP 1 2) (by simpa using hP 2 1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [J_279, powerTable, finitePower, power_02, power_01]
      rw [Rat.le_iff]
      norm_num [qJlo_279, qJhi_279]
  have hmain : termBound_279.mem ((c .t279 * 2) * ((x 1 ^ 2) * (x 2 ^ 1))) := by
    refine mem_mul_of_bounds hcI hJmem ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [I_279, J_279, termBound_279]
      rw [Rat.le_iff]
      norm_num [qIlo_279, qIhi_279, qJlo_279, qJhi_279]
  simpa using hmain

private def termBound_280 : RatInterval := ⟨(-128468801040123394200370849475920745872123962469512603471711370213101473699533522937416517107302768971319508022622979939182634758283530670194623714315019994348458464407824496511467511 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ), (0 : ℚ), by norm_num⟩
private def qAlo_280 : ℚ := (-32117200260030848550092712368980186468030990617378150867927842553275368424883380734354129276825692242746590722788297812898391068229544201979421748750560878839241469668142959463417340172102764785 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def qAhi_280 : ℚ := (-32117200260030848550092712368980186468030990617378150867927842553275368424883380734354129276825692242746590722788297812898391068179249528328085983877295645333299627492240746766471326383876854495 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def qIlo_280 : ℚ := (-32117200260030848550092712368980186468030990617378150867927842553275368424883380734354129276825692242746590722788297812898391068229544201979421748750560878839241469668142959463417340172102764785 / 1140610154405548804660292901425072831223307126812139982644798129474818791802169346626478202829342849944660577393398601827672176180343859499563165329930553547062998668590066237520718548061650944 : ℚ)
private def qIhi_280 : ℚ := (-32117200260030848550092712368980186468030990617378150867927842553275368424883380734354129276825692242746590722788297812898391068179249528328085983877295645333299627492240746766471326383876854495 / 1140610154405548804660292901425072831223307126812139982644798129474818791802169346626478202829342849944660577393398601827672176180343859499563165329930553547062998668590066237520718548061650944 : ℚ)
private def I_280 : RatInterval :=
  { lo := qIlo_280, hi := qIhi_280, h := by rw [Rat.le_iff]; norm_num [qIlo_280, qIhi_280] }
private def qJlo_280 : ℚ := (0 : ℚ)
private def qJhi_280 : ℚ := (5203966097332199540962620163682042769307631123633352402659556175201804029836680149006119720866162092434705725242304330282309107461355592549428349480868442707252758566117640553861636996282755545060734484677007017918912818113029444244317480593190824521093569024285556127802533255360063033138403712736567687719505396167812814121946891420490198322371509864809928481057607989849 / 5203966097332199540962620163682042769307631123633352402659556175201804029836680149006119720866162092421210806977140503895691783124161732454069953302838660381462064754694610172886591674830791775236479710273844905605846838573774239433481250692219130145866174442655580414269208292514127802333112415945459400923534111101570260513349217744366479014439025434868093450357360355277851584364544 : ℚ)
private def J_280 : RatInterval :=
  { lo := qJlo_280, hi := qJhi_280, h := by rw [Rat.le_iff]; norm_num [qJlo_280, qJhi_280] }
private theorem term_mem_280 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_280.mem (hessianTerm c x .t280) := by
  have hterm : hessianTerm c x .t280 =
      (c .t280 * 2) * ((x 1 ^ 2) * (x 2 ^ 2)) := by
    unfold hessianTerm derivativeCoeff monomial
    rw [show exponents .t280 = ![2, 2, 2] from rfl]
    norm_num [lowerExponent]
    try ring
    try simp
  rw [hterm]
  have hcI : I_280.mem (c .t280 * 2) := by
    constructor
    · have h := (hC .t280).1
      rw [show (coefficientInterval .t280).lo = qAlo_280 from rfl] at h
      norm_num [I_280, qIlo_280, qAlo_280] at h ⊢
      linarith
    · have h := (hC .t280).2
      rw [show (coefficientInterval .t280).hi = qAhi_280 from rfl] at h
      norm_num [I_280, qIhi_280, qAhi_280] at h ⊢
      linarith
  have hJmem : J_280.mem ((x 1 ^ 2) * (x 2 ^ 2)) := by
    refine mem_mul_of_bounds (by simpa using hP 1 2) (by simpa using hP 2 2) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [J_280, powerTable, finitePower, power_02, power_02]
      rw [Rat.le_iff]
      norm_num [qJlo_280, qJhi_280]
  have hmain : termBound_280.mem ((c .t280 * 2) * ((x 1 ^ 2) * (x 2 ^ 2))) := by
    refine mem_mul_of_bounds hcI hJmem ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [I_280, J_280, termBound_280]
      rw [Rat.le_iff]
      norm_num [qIlo_280, qIhi_280, qJlo_280, qJhi_280]
  simpa using hmain

private def termBound_281 : RatInterval := ⟨(-229353102254887726601536362899808676057512435541580552563336573214177933643481602908575609231225149444734160419020595260532238755660527731484108034409507282040740577217457105190613 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ), (229353102254887726601536362899808676057512435541580552563336573214177933643481602908575609231225149444845844412807086194475172892039647917114393726209830951644376541883128417957445 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ), by norm_num⟩
private def qAlo_281 : ℚ := (-28669137781860965825192045362476084507189054442697569070417071651772241705435200363571951153903143680512799587057979040503942952788146800895282818340471682581130432412089098573694955691341983909 / 1140610154405548804660292901425072831223307126812139982644798129474818791802169346626478202829342849944660577393398601827672176180343859499563165329930553547062998668590066237520718548061650944 : ℚ)
private def qAhi_281 : ℚ := (-114676551127443863300768181449904338028756217770790276281668286607088966821740801454287804615612574722051198348231916162015771811005645266853559696566442417785379642218088964956200422315778897343 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qIlo_281 : ℚ := (-28669137781860965825192045362476084507189054442697569070417071651772241705435200363571951153903143680512799587057979040503942952788146800895282818340471682581130432412089098573694955691341983909 / 570305077202774402330146450712536415611653563406069991322399064737409395901084673313239101414671424972330288696699300913836088090171929749781582664965276773531499334295033118760359274030825472 : ℚ)
private def qIhi_281 : ℚ := (-114676551127443863300768181449904338028756217770790276281668286607088966821740801454287804615612574722051198348231916162015771811005645266853559696566442417785379642218088964956200422315778897343 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def I_281 : RatInterval :=
  { lo := qIlo_281, hi := qIhi_281, h := by rw [Rat.le_iff]; norm_num [qIlo_281, qIhi_281] }
private def qJlo_281 : ℚ := (-10407932194664399081925240327364085538615262247266704805319112350403608059673360298012239441732324184876158909617190573757926877091308115146535897050751776577400864037946796298210796653296744088687804916413693212217196960042096446199079213321864364665320515695797312171192956761446411048469075145379902290045300089096384820791321908951060566734326846426082557584323433277 / 10407932194664399081925240327364085538615262247266704805319112350403608059673360298012239441732324184842421613954281007791383566248323464908139906605677320762924129509389220345773183349661583550472959420547689811211693677147548478866962501384438260291732348885311160828538416585028255604666224831890918801847068222203140521026698435488732958028878050869736186900714720710555703168729088 : ℚ)
private def qJhi_281 : ℚ := (10407932194664399081925240327364085538615262247266704805319112350403608059673360298012239441732324184871090744316041498543061888309981043924115363192847941630027210242647918889083420495365956642582442232024314968690180845181333918800196544185793681982158535006814112855679321649902612076471019406936162416495123253164686652451642777867592935313545826817664501112809013399 / 10407932194664399081925240327364085538615262247266704805319112350403608059673360298012239441732324184842421613954281007791383566248323464908139906605677320762924129509389220345773183349661583550472959420547689811211693677147548478866962501384438260291732348885311160828538416585028255604666224831890918801847068222203140521026698435488732958028878050869736186900714720710555703168729088 : ℚ)
private def J_281 : RatInterval :=
  { lo := qJlo_281, hi := qJhi_281, h := by rw [Rat.le_iff]; norm_num [qJlo_281, qJhi_281] }
private theorem term_mem_281 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_281.mem (hessianTerm c x .t281) := by
  have hterm : hessianTerm c x .t281 =
      (c .t281 * 2) * ((x 1 ^ 2) * (x 2 ^ 3)) := by
    unfold hessianTerm derivativeCoeff monomial
    rw [show exponents .t281 = ![2, 2, 3] from rfl]
    norm_num [lowerExponent]
    try ring
    try simp
  rw [hterm]
  have hcI : I_281.mem (c .t281 * 2) := by
    constructor
    · have h := (hC .t281).1
      rw [show (coefficientInterval .t281).lo = qAlo_281 from rfl] at h
      norm_num [I_281, qIlo_281, qAlo_281] at h ⊢
      linarith
    · have h := (hC .t281).2
      rw [show (coefficientInterval .t281).hi = qAhi_281 from rfl] at h
      norm_num [I_281, qIhi_281, qAhi_281] at h ⊢
      linarith
  have hJmem : J_281.mem ((x 1 ^ 2) * (x 2 ^ 3)) := by
    refine mem_mul_of_bounds (by simpa using hP 1 2) (by simpa using hP 2 3) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [J_281, powerTable, finitePower, power_02, power_03]
      rw [Rat.le_iff]
      norm_num [qJlo_281, qJhi_281]
  have hmain : termBound_281.mem ((c .t281 * 2) * ((x 1 ^ 2) * (x 2 ^ 3))) := by
    refine mem_mul_of_bounds hcI hJmem ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [I_281, J_281, termBound_281]
      rw [Rat.le_iff]
      norm_num [qIlo_281, qIhi_281, qJlo_281, qJhi_281]
  simpa using hmain

private def termBound_282 : RatInterval := ⟨(-132865173849329420440017320212396573526458435278741632307554510799235060591084563591592232140786439201242888177576585091398820211715018249831941216442769457599897882737402699271 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ), (0 : ℚ), by norm_num⟩
private def qAlo_282 : ℚ := (-66432586924664710220008660106198286763229217639370816153777255399617530295542281795796116070393219600363034738902827945214858986081135333790979962302902998283208216105038505378116916550928039889 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qAhi_282 : ℚ := (-66432586924664710220008660106198286763229217639370816153777255399617530295542281795796116070393219600363034738902827945214858985939526169994091941460523324616114791941896639069743161953342771499 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qIlo_282 : ℚ := (-66432586924664710220008660106198286763229217639370816153777255399617530295542281795796116070393219600363034738902827945214858986081135333790979962302902998283208216105038505378116916550928039889 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def qIhi_282 : ℚ := (-66432586924664710220008660106198286763229217639370816153777255399617530295542281795796116070393219600363034738902827945214858985939526169994091941460523324616114791941896639069743161953342771499 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def I_282 : RatInterval :=
  { lo := qIlo_282, hi := qIhi_282, h := by rw [Rat.le_iff]; norm_num [qIlo_282, qIhi_282] }
private def qJlo_282 : ℚ := (0 : ℚ)
private def qJhi_282 : ℚ := (2601983048666099770481310081841021384653815561816676201329778087600902014918340074503059860433081046220726592187443121737808884814976261298553773784941666935074052735914577872174579856688049356711429532610199812658416511998782683124923417569364155006461362391953925122092169057616967626933759477674676795789445062464587583343604118190103593771642597866908951907607687 / 2601983048666099770481310081841021384653815561816676201329778087600902014918340074503059860433081046210605403488570251947845891562080866227034976651419330190731032377347305086443295837415395887618239855136922452802923419286887119716740625346109565072933087221327790207134604146257063901166556207972729700461767055550785130256674608872183239507219512717434046725178680177638925792182272 : ℚ)
private def J_282 : RatInterval :=
  { lo := qJlo_282, hi := qJhi_282, h := by rw [Rat.le_iff]; norm_num [qJlo_282, qJhi_282] }
private theorem term_mem_282 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_282.mem (hessianTerm c x .t282) := by
  have hterm : hessianTerm c x .t282 =
      (c .t282 * 2) * ((x 1 ^ 2) * (x 2 ^ 4)) := by
    unfold hessianTerm derivativeCoeff monomial
    rw [show exponents .t282 = ![2, 2, 4] from rfl]
    norm_num [lowerExponent]
    try ring
    try simp
  rw [hterm]
  have hcI : I_282.mem (c .t282 * 2) := by
    constructor
    · have h := (hC .t282).1
      rw [show (coefficientInterval .t282).lo = qAlo_282 from rfl] at h
      norm_num [I_282, qIlo_282, qAlo_282] at h ⊢
      linarith
    · have h := (hC .t282).2
      rw [show (coefficientInterval .t282).hi = qAhi_282 from rfl] at h
      norm_num [I_282, qIhi_282, qAhi_282] at h ⊢
      linarith
  have hJmem : J_282.mem ((x 1 ^ 2) * (x 2 ^ 4)) := by
    refine mem_mul_of_bounds (by simpa using hP 1 2) (by simpa using hP 2 4) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [J_282, powerTable, finitePower, power_02, power_04]
      rw [Rat.le_iff]
      norm_num [qJlo_282, qJhi_282]
  have hmain : termBound_282.mem ((c .t282 * 2) * ((x 1 ^ 2) * (x 2 ^ 4))) := by
    refine mem_mul_of_bounds hcI hJmem ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [I_282, J_282, termBound_282]
      rw [Rat.le_iff]
      norm_num [qIlo_282, qIhi_282, qJlo_282, qJhi_282]
  simpa using hmain

private def termBound_283 : RatInterval := ⟨(-413208571271260783946250588923192862861127310439796389263651341602680156954335061706706345851674045813072638871900172558210791015377905420423817666413880563881676708559224821 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ), (25825535704453798996640661807699553928820456902487274328978208850167509809645941356669146615729627863304464128509200303431992961925081096663085041507111716168050303796679851 / 285152538601387201165073225356268207805826781703034995661199532368704697950542336656619550707335712486165144348349650456918044045085964874890791332482638386765749667147516559380179637015412736 : ℚ), by norm_num⟩
private def qAlo_283 : ℚ := (25825535704453798996640661807699553928820456902487274328978208850167509809645941356669146615729627863199841123392277392166710717340890741051508915891879122677059447984016042541468784735912550135 / 570305077202774402330146450712536415611653563406069991322399064737409395901084673313239101414671424972330288696699300913836088090171929749781582664965276773531499334295033118760359274030825472 : ℚ)
private def qAhi_283 : ℚ := (206604285635630391973125294461596431430563655219898194631825670801340078477167530853353172925837022905598728987138219137333685738820264825988994788937950656259693832505248405590403715811306368777 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qIlo_283 : ℚ := (25825535704453798996640661807699553928820456902487274328978208850167509809645941356669146615729627863199841123392277392166710717340890741051508915891879122677059447984016042541468784735912550135 / 285152538601387201165073225356268207805826781703034995661199532368704697950542336656619550707335712486165144348349650456918044045085964874890791332482638386765749667147516559380179637015412736 : ℚ)
private def qIhi_283 : ℚ := (206604285635630391973125294461596431430563655219898194631825670801340078477167530853353172925837022905598728987138219137333685738820264825988994788937950656259693832505248405590403715811306368777 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def I_283 : RatInterval :=
  { lo := qIlo_283, hi := qIhi_283, h := by rw [Rat.le_iff]; norm_num [qIlo_283, qIhi_283] }
private def qJlo_283 : ℚ := (-10407932194664399081925240327364085538615262247266704805319112350403608059673360298012239441732324184889653827882354400144544201428501975241894293228781558903191557849369826679185873021775243111743430874902687597368180452153345736446919154968103543939762461659918629499541250201980574548348265794446401208846954536177821613591971710769106965298114024753783975438725 / 10407932194664399081925240327364085538615262247266704805319112350403608059673360298012239441732324184842421613954281007791383566248323464908139906605677320762924129509389220345773183349661583550472959420547689811211693677147548478866962501384438260291732348885311160828538416585028255604666224831890918801847068222203140521026698435488732958028878050869736186900714720710555703168729088 : ℚ)
private def qJhi_283 : ℚ := (10407932194664399081925240327364085538615262247266704805319112350403608059673360298012239441732324184884585662581205324929679212647174904019473759370877723955817904054070949270059416546936834094883656221962071601465562339615388852013162847722213443446980904532475132570794536865091147417699874888737497347051980386576571246666204107045585101156162682901373577578469 / 10407932194664399081925240327364085538615262247266704805319112350403608059673360298012239441732324184842421613954281007791383566248323464908139906605677320762924129509389220345773183349661583550472959420547689811211693677147548478866962501384438260291732348885311160828538416585028255604666224831890918801847068222203140521026698435488732958028878050869736186900714720710555703168729088 : ℚ)
private def J_283 : RatInterval :=
  { lo := qJlo_283, hi := qJhi_283, h := by rw [Rat.le_iff]; norm_num [qJlo_283, qJhi_283] }
private theorem term_mem_283 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_283.mem (hessianTerm c x .t283) := by
  have hterm : hessianTerm c x .t283 =
      (c .t283 * 2) * ((x 1 ^ 2) * (x 2 ^ 5)) := by
    unfold hessianTerm derivativeCoeff monomial
    rw [show exponents .t283 = ![2, 2, 5] from rfl]
    norm_num [lowerExponent]
    try ring
    try simp
  rw [hterm]
  have hcI : I_283.mem (c .t283 * 2) := by
    constructor
    · have h := (hC .t283).1
      rw [show (coefficientInterval .t283).lo = qAlo_283 from rfl] at h
      norm_num [I_283, qIlo_283, qAlo_283] at h ⊢
      linarith
    · have h := (hC .t283).2
      rw [show (coefficientInterval .t283).hi = qAhi_283 from rfl] at h
      norm_num [I_283, qIhi_283, qAhi_283] at h ⊢
      linarith
  have hJmem : J_283.mem ((x 1 ^ 2) * (x 2 ^ 5)) := by
    refine mem_mul_of_bounds (by simpa using hP 1 2) (by simpa using hP 2 5) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [J_283, powerTable, finitePower, power_02, power_05]
      rw [Rat.le_iff]
      norm_num [qJlo_283, qJhi_283]
  have hmain : termBound_283.mem ((c .t283 * 2) * ((x 1 ^ 2) * (x 2 ^ 5))) := by
    refine mem_mul_of_bounds hcI hJmem ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [I_283, J_283, termBound_283]
      rw [Rat.le_iff]
      norm_num [qIlo_283, qIhi_283, qJlo_283, qJhi_283]
  simpa using hmain

private def termBound_284 : RatInterval := ⟨(0 : ℚ), (739385061579395388518011745015205048507367842598433256460025370226873655926666136294767823978508719867858541109601234176131284222949023468628768090625001028957713925508249 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ), by norm_num⟩
private def qAlo_284 : ℚ := (369692530789697694259005872507602524253683921299216628230012685113436827963333068147383911989254359932011898153467674059949548722669915776830545538961485376802072989314247515147492973705144821297 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def qAhi_284 : ℚ := (184846265394848847129502936253801262126841960649608314115006342556718413981666534073691955994627179966005949076733837029974774361344100171912666134418241706281778790242376601637914579054220192603 / 1140610154405548804660292901425072831223307126812139982644798129474818791802169346626478202829342849944660577393398601827672176180343859499563165329930553547062998668590066237520718548061650944 : ℚ)
private def qIlo_284 : ℚ := (369692530789697694259005872507602524253683921299216628230012685113436827963333068147383911989254359932011898153467674059949548722669915776830545538961485376802072989314247515147492973705144821297 / 1140610154405548804660292901425072831223307126812139982644798129474818791802169346626478202829342849944660577393398601827672176180343859499563165329930553547062998668590066237520718548061650944 : ℚ)
private def qIhi_284 : ℚ := (184846265394848847129502936253801262126841960649608314115006342556718413981666534073691955994627179966005949076733837029974774361344100171912666134418241706281778790242376601637914579054220192603 / 570305077202774402330146450712536415611653563406069991322399064737409395901084673313239101414671424972330288696699300913836088090171929749781582664965276773531499334295033118760359274030825472 : ℚ)
private def I_284 : RatInterval :=
  { lo := qIlo_284, hi := qIhi_284, h := by rw [Rat.le_iff]; norm_num [qIlo_284, qIhi_284] }
private def qJlo_284 : ℚ := (0 : ℚ)
private def qJhi_284 : ℚ := (10407932194664399081925240327364085538615262247266704805319112350403608059673360298012239441732324184896401287014936313337852863597098905289573491317796450066086904755081341871513376793954202928805192586854600830188285835171774486317982556662205955835929307536899088884405997021409384708089832104552938220896922706301746029857134447518473936718774297330528689805 / 10407932194664399081925240327364085538615262247266704805319112350403608059673360298012239441732324184842421613954281007791383566248323464908139906605677320762924129509389220345773183349661583550472959420547689811211693677147548478866962501384438260291732348885311160828538416585028255604666224831890918801847068222203140521026698435488732958028878050869736186900714720710555703168729088 : ℚ)
private def J_284 : RatInterval :=
  { lo := qJlo_284, hi := qJhi_284, h := by rw [Rat.le_iff]; norm_num [qJlo_284, qJhi_284] }
private theorem term_mem_284 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_284.mem (hessianTerm c x .t284) := by
  have hterm : hessianTerm c x .t284 =
      (c .t284 * 2) * ((x 1 ^ 2) * (x 2 ^ 6)) := by
    unfold hessianTerm derivativeCoeff monomial
    rw [show exponents .t284 = ![2, 2, 6] from rfl]
    norm_num [lowerExponent]
    try ring
    try simp
  rw [hterm]
  have hcI : I_284.mem (c .t284 * 2) := by
    constructor
    · have h := (hC .t284).1
      rw [show (coefficientInterval .t284).lo = qAlo_284 from rfl] at h
      norm_num [I_284, qIlo_284, qAlo_284] at h ⊢
      linarith
    · have h := (hC .t284).2
      rw [show (coefficientInterval .t284).hi = qAhi_284 from rfl] at h
      norm_num [I_284, qIhi_284, qAhi_284] at h ⊢
      linarith
  have hJmem : J_284.mem ((x 1 ^ 2) * (x 2 ^ 6)) := by
    refine mem_mul_of_bounds (by simpa using hP 1 2) (by simpa using hP 2 6) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [J_284, powerTable, finitePower, power_02, power_06]
      rw [Rat.le_iff]
      norm_num [qJlo_284, qJhi_284]
  have hmain : termBound_284.mem ((c .t284 * 2) * ((x 1 ^ 2) * (x 2 ^ 6))) := by
    refine mem_mul_of_bounds hcI hJmem ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [I_284, J_284, termBound_284]
      rw [Rat.le_iff]
      norm_num [qIlo_284, qIhi_284, qJlo_284, qJhi_284]
  simpa using hmain

private def termBound_285 : RatInterval := ⟨(-1631787263256902207598960730879570782909074949869573805580383618614723627647292489473063706269806603200852729994210702763135475612721457977382236192700169299420170721947 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ), (815893631628451103799480365439785391454537474934786902790191809307361813823646244736531853134903301600029063812210270868459471744558369386233932630502293044632489610319 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ), by norm_num⟩
private def qAlo_285 : ℚ := (815893631628451103799480365439785391454537474934786902790191809307361813823646244736531853134903301595665872759375225886181036758209217011132338807854108396489710854615246344447995962923441390837 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qAhi_285 : ℚ := (203973407907112775949870091359946347863634368733696725697547952326840453455911561184132963283725825398916468189843806471545259189554363781792456241807769778013290198072277451231539364723830283021 / 1140610154405548804660292901425072831223307126812139982644798129474818791802169346626478202829342849944660577393398601827672176180343859499563165329930553547062998668590066237520718548061650944 : ℚ)
private def qIlo_285 : ℚ := (815893631628451103799480365439785391454537474934786902790191809307361813823646244736531853134903301595665872759375225886181036758209217011132338807854108396489710854615246344447995962923441390837 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def qIhi_285 : ℚ := (203973407907112775949870091359946347863634368733696725697547952326840453455911561184132963283725825398916468189843806471545259189554363781792456241807769778013290198072277451231539364723830283021 / 570305077202774402330146450712536415611653563406069991322399064737409395901084673313239101414671424972330288696699300913836088090171929749781582664965276773531499334295033118760359274030825472 : ℚ)
private def I_285 : RatInterval :=
  { lo := qIlo_285, hi := qIhi_285, h := by rw [Rat.le_iff]; norm_num [qIlo_285, qIhi_285] }
private def qJlo_285 : ℚ := (-5203966097332199540962620163682042769307631123633352402659556175201804029836680149006119720866162092451574373073759113265580762882847917668626344703405670614491125830396429033988514998529026464277905034184690515223410153628818478768539620756515865385940228016982704540624346962369897982487397685382137377287496030369910892044410154871871657398229777290472267 / 5203966097332199540962620163682042769307631123633352402659556175201804029836680149006119720866162092421210806977140503895691783124161732454069953302838660381462064754694610172886591674830791775236479710273844905605846838573774239433481250692219130145866174442655580414269208292514127802333112415945459400923534111101570260513349217744366479014439025434868093450357360355277851584364544 : ℚ)
private def qJhi_285 : ℚ := (5203966097332199540962620163682042769307631123633352402659556175201804029836680149006119720866162092449040290423184575658148268492184382057416077774453753140804298932746989859274905996377849065312566083510762069674689882410236310227030882649063384619762124791957575443762985294795782748016009549923324085091740899268020679560004117380914195759727051803456197 / 5203966097332199540962620163682042769307631123633352402659556175201804029836680149006119720866162092421210806977140503895691783124161732454069953302838660381462064754694610172886591674830791775236479710273844905605846838573774239433481250692219130145866174442655580414269208292514127802333112415945459400923534111101570260513349217744366479014439025434868093450357360355277851584364544 : ℚ)
private def J_285 : RatInterval :=
  { lo := qJlo_285, hi := qJhi_285, h := by rw [Rat.le_iff]; norm_num [qJlo_285, qJhi_285] }
private theorem term_mem_285 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_285.mem (hessianTerm c x .t285) := by
  have hterm : hessianTerm c x .t285 =
      (c .t285 * 2) * ((x 1 ^ 2) * (x 2 ^ 7)) := by
    unfold hessianTerm derivativeCoeff monomial
    rw [show exponents .t285 = ![2, 2, 7] from rfl]
    norm_num [lowerExponent]
    try ring
    try simp
  rw [hterm]
  have hcI : I_285.mem (c .t285 * 2) := by
    constructor
    · have h := (hC .t285).1
      rw [show (coefficientInterval .t285).lo = qAlo_285 from rfl] at h
      norm_num [I_285, qIlo_285, qAlo_285] at h ⊢
      linarith
    · have h := (hC .t285).2
      rw [show (coefficientInterval .t285).hi = qAhi_285 from rfl] at h
      norm_num [I_285, qIhi_285, qAhi_285] at h ⊢
      linarith
  have hJmem : J_285.mem ((x 1 ^ 2) * (x 2 ^ 7)) := by
    refine mem_mul_of_bounds (by simpa using hP 1 2) (by simpa using hP 2 7) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [J_285, powerTable, finitePower, power_02, power_07]
      rw [Rat.le_iff]
      norm_num [qJlo_285, qJhi_285]
  have hmain : termBound_285.mem ((c .t285 * 2) * ((x 1 ^ 2) * (x 2 ^ 7))) := by
    refine mem_mul_of_bounds hcI hJmem ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [I_285, J_285, termBound_285]
      rw [Rat.le_iff]
      norm_num [qIlo_285, qIhi_285, qJlo_285, qJhi_285]
  simpa using hmain

private def termBound_286 : RatInterval := ⟨(0 : ℚ), (291131237414817294545447927997256521395505055218437384760355229694168685292836586186576229544053117890154850226149919886511097259127882974738337919076249859897363069 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ), by norm_num⟩
private def qAlo_286 : ℚ := (72782809353704323636361981999314130348876263804609346190088807423542171323209146546644057386013279472066861834911544276248050581328252595665314276048674714505815161443571452440989955036240031315 / 1140610154405548804660292901425072831223307126812139982644798129474818791802169346626478202829342849944660577393398601827672176180343859499563165329930553547062998668590066237520718548061650944 : ℚ)
private def qAhi_286 : ℚ := (36391404676852161818180990999657065174438131902304673095044403711771085661604573273322028693006639736033430917455772138124025290664180816760597516747953825323392459679191118988649889486785446061 / 570305077202774402330146450712536415611653563406069991322399064737409395901084673313239101414671424972330288696699300913836088090171929749781582664965276773531499334295033118760359274030825472 : ℚ)
private def qIlo_286 : ℚ := (72782809353704323636361981999314130348876263804609346190088807423542171323209146546644057386013279472066861834911544276248050581328252595665314276048674714505815161443571452440989955036240031315 / 570305077202774402330146450712536415611653563406069991322399064737409395901084673313239101414671424972330288696699300913836088090171929749781582664965276773531499334295033118760359274030825472 : ℚ)
private def qIhi_286 : ℚ := (36391404676852161818180990999657065174438131902304673095044403711771085661604573273322028693006639736033430917455772138124025290664180816760597516747953825323392459679191118988649889486785446061 / 285152538601387201165073225356268207805826781703034995661199532368704697950542336656619550707335712486165144348349650456918044045085964874890791332482638386765749667147516559380179637015412736 : ℚ)
private def I_286 : RatInterval :=
  { lo := qIlo_286, hi := qIhi_286, h := by rw [Rat.le_iff]; norm_num [qIlo_286, qIhi_286] }
private def qJlo_286 : ℚ := (0 : ℚ)
private def qJhi_286 : ℚ := (10407932194664399081925240327364085538615262247266704805319112350403608059673360298012239441732324184909896205280100139724470187934292765384931887495826232391877598566505666838085960200233808112031109485168688419040672100736031993340440675263291478076509128424824025475935854484356242680270314173571240179731570076875768525772089613846543556667435414142185 / 10407932194664399081925240327364085538615262247266704805319112350403608059673360298012239441732324184842421613954281007791383566248323464908139906605677320762924129509389220345773183349661583550472959420547689811211693677147548478866962501384438260291732348885311160828538416585028255604666224831890918801847068222203140521026698435488732958028878050869736186900714720710555703168729088 : ℚ)
private def J_286 : RatInterval :=
  { lo := qJlo_286, hi := qJhi_286, h := by rw [Rat.le_iff]; norm_num [qJlo_286, qJhi_286] }
private theorem term_mem_286 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_286.mem (hessianTerm c x .t286) := by
  have hterm : hessianTerm c x .t286 =
      (c .t286 * 2) * ((x 1 ^ 2) * (x 2 ^ 8)) := by
    unfold hessianTerm derivativeCoeff monomial
    rw [show exponents .t286 = ![2, 2, 8] from rfl]
    norm_num [lowerExponent]
    try ring
    try simp
  rw [hterm]
  have hcI : I_286.mem (c .t286 * 2) := by
    constructor
    · have h := (hC .t286).1
      rw [show (coefficientInterval .t286).lo = qAlo_286 from rfl] at h
      norm_num [I_286, qIlo_286, qAlo_286] at h ⊢
      linarith
    · have h := (hC .t286).2
      rw [show (coefficientInterval .t286).hi = qAhi_286 from rfl] at h
      norm_num [I_286, qIhi_286, qAhi_286] at h ⊢
      linarith
  have hJmem : J_286.mem ((x 1 ^ 2) * (x 2 ^ 8)) := by
    refine mem_mul_of_bounds (by simpa using hP 1 2) (by simpa using hP 2 8) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [J_286, powerTable, finitePower, power_02, power_08]
      rw [Rat.le_iff]
      norm_num [qJlo_286, qJhi_286]
  have hmain : termBound_286.mem ((c .t286 * 2) * ((x 1 ^ 2) * (x 2 ^ 8))) := by
    refine mem_mul_of_bounds hcI hJmem ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [I_286, J_286, termBound_286]
      rw [Rat.le_iff]
      norm_num [qIlo_286, qIhi_286, qJlo_286, qJhi_286]
  simpa using hmain

private def termBound_287 : RatInterval := ⟨(-5941200735729538634095669907237700160989343669404552859062516659460388734031147479651528104918462833033325929110261613372423502780277986895382207582901082406508054699204703950745492641 / 1140610154405548804660292901425072831223307126812139982644798129474818791802169346626478202829342849944660577393398601827672176180343859499563165329930553547062998668590066237520718548061650944 : ℚ), (23764802942918154536382679628950800643957374677618211436250066637841554936124589918606112419673851332121731393772986748694427685904307555402611706097116179008893941529569957004453793313 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ), by norm_num⟩
private def qAlo_287 : ℚ := (5941200735729538634095669907237700160989343669404552859062516659460388734031147479651528104918462833021770893466384625925980300909813076691380820000832139209982117935948499795370766135639414133 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def qAhi_287 : ℚ := (11882401471459077268191339814475400321978687338809105718125033318920777468062294959303056209836925666043541786932769251851960601831960296387773596260188416360689911699207406800265430628309508967 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ)
private def qIlo_287 : ℚ := (5941200735729538634095669907237700160989343669404552859062516659460388734031147479651528104918462833021770893466384625925980300909813076691380820000832139209982117935948499795370766135639414133 / 1140610154405548804660292901425072831223307126812139982644798129474818791802169346626478202829342849944660577393398601827672176180343859499563165329930553547062998668590066237520718548061650944 : ℚ)
private def qIhi_287 : ℚ := (11882401471459077268191339814475400321978687338809105718125033318920777468062294959303056209836925666043541786932769251851960601831960296387773596260188416360689911699207406800265430628309508967 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888 : ℚ)
private def I_287 : RatInterval :=
  { lo := qIlo_287, hi := qIhi_287, h := by rw [Rat.le_iff]; norm_num [qIlo_287, qIhi_287] }
private theorem term_mem_287 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    termBound_287.mem (hessianTerm c x .t287) := by
  have hterm : hessianTerm c x .t287 =
      (c .t287 * 2) * ((x 1 ^ 3)) := by
    unfold hessianTerm derivativeCoeff monomial
    rw [show exponents .t287 = ![2, 3, 0] from rfl]
    norm_num [lowerExponent]
    try ring
    try simp
  rw [hterm]
  have hcI : I_287.mem (c .t287 * 2) := by
    constructor
    · have h := (hC .t287).1
      rw [show (coefficientInterval .t287).lo = qAlo_287 from rfl] at h
      norm_num [I_287, qIlo_287, qAlo_287] at h ⊢
      linarith
    · have h := (hC .t287).2
      rw [show (coefficientInterval .t287).hi = qAhi_287 from rfl] at h
      norm_num [I_287, qIhi_287, qAhi_287] at h ⊢
      linarith
  have hJmem : power_03.mem (x 1 ^ 3) := by
    simpa [powerTable, finitePower, power_03] using hP 1 3
  have hmain : termBound_287.mem ((c .t287 * 2) * ((x 1 ^ 3))) := by
    refine mem_mul_of_bounds hcI hJmem ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals
      simp only [I_287, power_03, termBound_287]
      rw [Rat.le_iff]
      norm_num [qIlo_287, qIhi_287]
  simpa using hmain

def block_08 : List TermIndex := [.t192, .t193, .t194, .t195, .t196, .t197, .t198, .t199, .t200, .t201, .t202, .t203, .t204, .t205, .t206, .t207, .t208, .t209, .t210, .t211, .t212, .t213, .t214, .t215]
private def blockBound_08 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem block_mem_08 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    blockBound_08.mem (formalHessianEntry exponents c 0 0 x block_08) := by
  have h : (sumIntervals [termBound_192, termBound_193, termBound_194, termBound_195, termBound_196, termBound_197, termBound_198, termBound_199, termBound_200, termBound_201, termBound_202, termBound_203, termBound_204, termBound_205, termBound_206, termBound_207, termBound_208, termBound_209, termBound_210, termBound_211, termBound_212, termBound_213, termBound_214, termBound_215]).mem
      (formalHessianEntry exponents c 0 0 x block_08) := by
    exact (mem_add (term_mem_192 c x hC hP) (mem_add (term_mem_193 c x hC hP) (mem_add (term_mem_194 c x hC hP) (mem_add (term_mem_195 c x hC hP) (mem_add (term_mem_196 c x hC hP) (mem_add (term_mem_197 c x hC hP) (mem_add (term_mem_198 c x hC hP) (mem_add (term_mem_199 c x hC hP) (mem_add (term_mem_200 c x hC hP) (mem_add (term_mem_201 c x hC hP) (mem_add (term_mem_202 c x hC hP) (mem_add (term_mem_203 c x hC hP) (mem_add (term_mem_204 c x hC hP) (mem_add (term_mem_205 c x hC hP) (mem_add (term_mem_206 c x hC hP) (mem_add (term_mem_207 c x hC hP) (mem_add (term_mem_208 c x hC hP) (mem_add (term_mem_209 c x hC hP) (mem_add (term_mem_210 c x hC hP) (mem_add (term_mem_211 c x hC hP) (mem_add (term_mem_212 c x hC hP) (mem_add (term_mem_213 c x hC hP) (mem_add (term_mem_214 c x hC hP) (mem_add (term_mem_215 c x hC hP) (by simpa [sumIntervals, eval] using mem_const (0 : ℚ))))))))))))))))))))))))))
  exact mem_subset h
    (by norm_num [blockBound_08, sumIntervals, RatInterval.add, RatInterval.const, termBound_192, termBound_193, termBound_194, termBound_195, termBound_196, termBound_197, termBound_198, termBound_199, termBound_200, termBound_201, termBound_202, termBound_203, termBound_204, termBound_205, termBound_206, termBound_207, termBound_208, termBound_209, termBound_210, termBound_211, termBound_212, termBound_213, termBound_214, termBound_215])
    (by norm_num [blockBound_08, sumIntervals, RatInterval.add, RatInterval.const, termBound_192, termBound_193, termBound_194, termBound_195, termBound_196, termBound_197, termBound_198, termBound_199, termBound_200, termBound_201, termBound_202, termBound_203, termBound_204, termBound_205, termBound_206, termBound_207, termBound_208, termBound_209, termBound_210, termBound_211, termBound_212, termBound_213, termBound_214, termBound_215])

def block_09 : List TermIndex := [.t216, .t217, .t218, .t219, .t220, .t221, .t222, .t223, .t224, .t225, .t226, .t227, .t228, .t229, .t230, .t231, .t232, .t233, .t234, .t235, .t236, .t237, .t238, .t239]
private def blockBound_09 : RatInterval := ⟨(0 : ℚ), (0 : ℚ), by norm_num⟩
private theorem block_mem_09 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    blockBound_09.mem (formalHessianEntry exponents c 0 0 x block_09) := by
  have h : (sumIntervals [termBound_216, termBound_217, termBound_218, termBound_219, termBound_220, termBound_221, termBound_222, termBound_223, termBound_224, termBound_225, termBound_226, termBound_227, termBound_228, termBound_229, termBound_230, termBound_231, termBound_232, termBound_233, termBound_234, termBound_235, termBound_236, termBound_237, termBound_238, termBound_239]).mem
      (formalHessianEntry exponents c 0 0 x block_09) := by
    exact (mem_add (term_mem_216 c x hC hP) (mem_add (term_mem_217 c x hC hP) (mem_add (term_mem_218 c x hC hP) (mem_add (term_mem_219 c x hC hP) (mem_add (term_mem_220 c x hC hP) (mem_add (term_mem_221 c x hC hP) (mem_add (term_mem_222 c x hC hP) (mem_add (term_mem_223 c x hC hP) (mem_add (term_mem_224 c x hC hP) (mem_add (term_mem_225 c x hC hP) (mem_add (term_mem_226 c x hC hP) (mem_add (term_mem_227 c x hC hP) (mem_add (term_mem_228 c x hC hP) (mem_add (term_mem_229 c x hC hP) (mem_add (term_mem_230 c x hC hP) (mem_add (term_mem_231 c x hC hP) (mem_add (term_mem_232 c x hC hP) (mem_add (term_mem_233 c x hC hP) (mem_add (term_mem_234 c x hC hP) (mem_add (term_mem_235 c x hC hP) (mem_add (term_mem_236 c x hC hP) (mem_add (term_mem_237 c x hC hP) (mem_add (term_mem_238 c x hC hP) (mem_add (term_mem_239 c x hC hP) (by simpa [sumIntervals, eval] using mem_const (0 : ℚ))))))))))))))))))))))))))
  exact mem_subset h
    (by norm_num [blockBound_09, sumIntervals, RatInterval.add, RatInterval.const, termBound_216, termBound_217, termBound_218, termBound_219, termBound_220, termBound_221, termBound_222, termBound_223, termBound_224, termBound_225, termBound_226, termBound_227, termBound_228, termBound_229, termBound_230, termBound_231, termBound_232, termBound_233, termBound_234, termBound_235, termBound_236, termBound_237, termBound_238, termBound_239])
    (by norm_num [blockBound_09, sumIntervals, RatInterval.add, RatInterval.const, termBound_216, termBound_217, termBound_218, termBound_219, termBound_220, termBound_221, termBound_222, termBound_223, termBound_224, termBound_225, termBound_226, termBound_227, termBound_228, termBound_229, termBound_230, termBound_231, termBound_232, termBound_233, termBound_234, termBound_235, termBound_236, termBound_237, termBound_238, termBound_239])

def block_10 : List TermIndex := [.t240, .t241, .t242, .t243, .t244, .t245, .t246, .t247, .t248, .t249, .t250, .t251, .t252, .t253, .t254, .t255, .t256, .t257, .t258, .t259, .t260, .t261, .t262, .t263]
private def blockBound_10 : RatInterval := ⟨(190056580960004423793483776786573447088643865609801441758240460538321254772523582884253653565597763738824702103447986298112258659750691186979980202136086761001391871652625281036340273640805713 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ), (24209674781725067907547289376133148882525401652668321648150221379815174309327810423224472750471915476946289013672324316635669594881955380865906907904861760924802701174578173491401505527146597 / 570305077202774402330146450712536415611653563406069991322399064737409395901084673313239101414671424972330288696699300913836088090171929749781582664965276773531499334295033118760359274030825472 : ℚ), by norm_num⟩
private theorem block_mem_10 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    blockBound_10.mem (formalHessianEntry exponents c 0 0 x block_10) := by
  have h : (sumIntervals [termBound_240, termBound_241, termBound_242, termBound_243, termBound_244, termBound_245, termBound_246, termBound_247, termBound_248, termBound_249, termBound_250, termBound_251, termBound_252, termBound_253, termBound_254, termBound_255, termBound_256, termBound_257, termBound_258, termBound_259, termBound_260, termBound_261, termBound_262, termBound_263]).mem
      (formalHessianEntry exponents c 0 0 x block_10) := by
    exact (mem_add (term_mem_240 c x hC hP) (mem_add (term_mem_241 c x hC hP) (mem_add (term_mem_242 c x hC hP) (mem_add (term_mem_243 c x hC hP) (mem_add (term_mem_244 c x hC hP) (mem_add (term_mem_245 c x hC hP) (mem_add (term_mem_246 c x hC hP) (mem_add (term_mem_247 c x hC hP) (mem_add (term_mem_248 c x hC hP) (mem_add (term_mem_249 c x hC hP) (mem_add (term_mem_250 c x hC hP) (mem_add (term_mem_251 c x hC hP) (mem_add (term_mem_252 c x hC hP) (mem_add (term_mem_253 c x hC hP) (mem_add (term_mem_254 c x hC hP) (mem_add (term_mem_255 c x hC hP) (mem_add (term_mem_256 c x hC hP) (mem_add (term_mem_257 c x hC hP) (mem_add (term_mem_258 c x hC hP) (mem_add (term_mem_259 c x hC hP) (mem_add (term_mem_260 c x hC hP) (mem_add (term_mem_261 c x hC hP) (mem_add (term_mem_262 c x hC hP) (mem_add (term_mem_263 c x hC hP) (by simpa [sumIntervals, eval] using mem_const (0 : ℚ))))))))))))))))))))))))))
  exact mem_subset h
    (by norm_num [blockBound_10, sumIntervals, RatInterval.add, RatInterval.const, termBound_240, termBound_241, termBound_242, termBound_243, termBound_244, termBound_245, termBound_246, termBound_247, termBound_248, termBound_249, termBound_250, termBound_251, termBound_252, termBound_253, termBound_254, termBound_255, termBound_256, termBound_257, termBound_258, termBound_259, termBound_260, termBound_261, termBound_262, termBound_263])
    (by norm_num [blockBound_10, sumIntervals, RatInterval.add, RatInterval.const, termBound_240, termBound_241, termBound_242, termBound_243, termBound_244, termBound_245, termBound_246, termBound_247, termBound_248, termBound_249, termBound_250, termBound_251, termBound_252, termBound_253, termBound_254, termBound_255, termBound_256, termBound_257, termBound_258, termBound_259, termBound_260, termBound_261, termBound_262, termBound_263])

def block_11 : List TermIndex := [.t264, .t265, .t266, .t267, .t268, .t269, .t270, .t271, .t272, .t273, .t274, .t275, .t276, .t277, .t278, .t279, .t280, .t281, .t282, .t283, .t284, .t285, .t286, .t287]
private def blockBound_11 : RatInterval := ⟨(-1808341205285894777415074434541798541983682759250915502206438344323454033553557839483707969724793218307654183678074442785839955505852597793073201729052363279057743702607564488651781873128853 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ), (1819097588651799116566769912596563935905385962593342732302084423630894592736617724730289169957752065495402970219941126996141866657062825918132429759649333745302802156241998636257422971518753 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ), by norm_num⟩
private theorem block_mem_11 (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hP : PowerEnclosures (fun _ n => powerTable n) x) :
    blockBound_11.mem (formalHessianEntry exponents c 0 0 x block_11) := by
  have h : (sumIntervals [termBound_264, termBound_265, termBound_266, termBound_267, termBound_268, termBound_269, termBound_270, termBound_271, termBound_272, termBound_273, termBound_274, termBound_275, termBound_276, termBound_277, termBound_278, termBound_279, termBound_280, termBound_281, termBound_282, termBound_283, termBound_284, termBound_285, termBound_286, termBound_287]).mem
      (formalHessianEntry exponents c 0 0 x block_11) := by
    exact (mem_add (term_mem_264 c x hC hP) (mem_add (term_mem_265 c x hC hP) (mem_add (term_mem_266 c x hC hP) (mem_add (term_mem_267 c x hC hP) (mem_add (term_mem_268 c x hC hP) (mem_add (term_mem_269 c x hC hP) (mem_add (term_mem_270 c x hC hP) (mem_add (term_mem_271 c x hC hP) (mem_add (term_mem_272 c x hC hP) (mem_add (term_mem_273 c x hC hP) (mem_add (term_mem_274 c x hC hP) (mem_add (term_mem_275 c x hC hP) (mem_add (term_mem_276 c x hC hP) (mem_add (term_mem_277 c x hC hP) (mem_add (term_mem_278 c x hC hP) (mem_add (term_mem_279 c x hC hP) (mem_add (term_mem_280 c x hC hP) (mem_add (term_mem_281 c x hC hP) (mem_add (term_mem_282 c x hC hP) (mem_add (term_mem_283 c x hC hP) (mem_add (term_mem_284 c x hC hP) (mem_add (term_mem_285 c x hC hP) (mem_add (term_mem_286 c x hC hP) (mem_add (term_mem_287 c x hC hP) (by simpa [sumIntervals, eval] using mem_const (0 : ℚ))))))))))))))))))))))))))
  exact mem_subset h
    (by norm_num [blockBound_11, sumIntervals, RatInterval.add, RatInterval.const, termBound_264, termBound_265, termBound_266, termBound_267, termBound_268, termBound_269, termBound_270, termBound_271, termBound_272, termBound_273, termBound_274, termBound_275, termBound_276, termBound_277, termBound_278, termBound_279, termBound_280, termBound_281, termBound_282, termBound_283, termBound_284, termBound_285, termBound_286, termBound_287])
    (by norm_num [blockBound_11, sumIntervals, RatInterval.add, RatInterval.const, termBound_264, termBound_265, termBound_266, termBound_267, termBound_268, termBound_269, termBound_270, termBound_271, termBound_272, termBound_273, termBound_274, termBound_275, termBound_276, termBound_277, termBound_278, termBound_279, termBound_280, termBound_281, termBound_282, termBound_283, termBound_284, termBound_285, termBound_286, termBound_287])

def chunkTerms_02 : List TermIndex :=
  block_08 ++ (block_09 ++ (block_10 ++ (block_11 ++ ([]))))

def chunkInterval_02 : RatInterval := ⟨(47062059938679632254017175588007912136665045712637631564008505548499450184742506261192486398968242630129261979942477963831604676061209647296726750101758599430583531987504429136922122941919215 / 1140610154405548804660292901425072831223307126812139982644798129474818791802169346626478202829342849944660577393398601827672176180343859499563165329930553547062998668590066237520718548061650944 : ℚ), (195496495842452342376945084921661754996108599183939915917503855462152289067359101110526071173733075881065715079598535660081498625712705872845387692998543421143724411552867386567469467188691529 / 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 : ℚ), by norm_num⟩

theorem chunk02_mem (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hx : ∀ j, (relativeBox j).mem (x j)) :
    chunkInterval_02.mem
      (formalHessianEntry exponents c 0 0 x chunkTerms_02) := by
  have hP := power_enclosures x hx
  have h : (sumIntervals [blockBound_08, blockBound_09, blockBound_10, blockBound_11]).mem
      (formalHessianEntry exponents c 0 0 x chunkTerms_02) := by
    simp only [chunkTerms_02, hessian_append, hessian_nil]
    exact (mem_add (block_mem_08 c x hC hP) (mem_add (block_mem_09 c x hC hP) (mem_add (block_mem_10 c x hC hP) (mem_add (block_mem_11 c x hC hP) (by simpa [sumIntervals, eval] using mem_const (0 : ℚ))))))
  exact mem_subset h
    (by norm_num [chunkInterval_02, sumIntervals, RatInterval.add, RatInterval.const, blockBound_08, blockBound_09, blockBound_10, blockBound_11])
    (by norm_num [chunkInterval_02, sumIntervals, RatInterval.add, RatInterval.const, blockBound_08, blockBound_09, blockBound_10, blockBound_11])

end ThomsonNine.LocalSparseHessianAAA
