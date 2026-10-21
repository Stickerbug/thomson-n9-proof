import ThomsonNine.LocalSparseHessianAAABase
import ThomsonNine.LocalSparseHessianAAAChunk00
import ThomsonNine.LocalSparseHessianAAAChunk01
import ThomsonNine.LocalSparseHessianAAAChunk02
import ThomsonNine.LocalSparseHessianAAAChunk03
import ThomsonNine.LocalSparseHessianAAAChunk04
import ThomsonNine.LocalSparseHessianAAAChunk05
import ThomsonNine.LocalSparseHessianAAAChunk06
import ThomsonNine.LocalSparseHessianAAAChunk07

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace ThomsonNine.LocalSparseHessianAAA

open ThomsonNine.Interval ThomsonNine.Interval.SparsePolynomial
open ThomsonNine.Interval.RatInterval

def terms : List TermIndex :=
  chunkTerms_00 ++ (chunkTerms_01 ++ (chunkTerms_02 ++ (chunkTerms_03 ++ (chunkTerms_04 ++ (chunkTerms_05 ++ (chunkTerms_06 ++ (chunkTerms_07 ++ ([]))))))))

private theorem formal_h00_mem (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hx : ∀ j, (relativeBox j).mem (x j)) :
    targetH00.mem (formalHessianEntry exponents c 0 0 x terms) := by
  have h : (sumIntervals [chunkInterval_00, chunkInterval_01, chunkInterval_02, chunkInterval_03, chunkInterval_04, chunkInterval_05, chunkInterval_06, chunkInterval_07]).mem
      (formalHessianEntry exponents c 0 0 x terms) := by
    simp only [terms, hessian_append, hessian_nil]
    exact (mem_add (chunk00_mem c x hC hx) (mem_add (chunk01_mem c x hC hx) (mem_add (chunk02_mem c x hC hx) (mem_add (chunk03_mem c x hC hx) (mem_add (chunk04_mem c x hC hx) (mem_add (chunk05_mem c x hC hx) (mem_add (chunk06_mem c x hC hx) (mem_add (chunk07_mem c x hC hx) (by simpa [sumIntervals, eval] using mem_const (0 : ℚ))))))))))
  exact mem_subset h
    (by norm_num [targetH00, sumIntervals, RatInterval.add, RatInterval.const, chunkInterval_00, chunkInterval_01, chunkInterval_02, chunkInterval_03, chunkInterval_04, chunkInterval_05, chunkInterval_06, chunkInterval_07])
    (by norm_num [targetH00, sumIntervals, RatInterval.add, RatInterval.const, chunkInterval_00, chunkInterval_01, chunkInterval_02, chunkInterval_03, chunkInterval_04, chunkInterval_05, chunkInterval_06, chunkInterval_07])

/-- Actual nested u-coordinate derivative belongs to archived AAA H00.
Only membership of one fixed real shifted coefficient family and the point
in the archived relative source box are premises. Power and arithmetic
endpoint bounds are discharged above, not assumed here. -/
theorem actual_h00_mem (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ k, (coefficientInterval k).mem (c k))
    (hx : ∀ i, (relativeBox i).mem (x i)) :
    targetH00.mem
      (axisDeriv (axisDeriv (fun y => eval exponents c y terms) 0) 0 x) := by
  rw [axisDeriv_axisDeriv_eval]
  exact formal_h00_mem c x hC hx

end ThomsonNine.LocalSparseHessianAAA
