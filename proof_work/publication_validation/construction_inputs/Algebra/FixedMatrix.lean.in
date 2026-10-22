import ThomsonNine.FixedIntervalSigned
import Mathlib.LinearAlgebra.Matrix.PosDef

-- Isolated source: Algebra.FixedMatrix
noncomputable section
namespace ThomsonNine.FixedInterval
open scoped BigOperators
def matrixMul3 (s : ℤ) (A B : Fin 3 → Fin 3 → Bounds) : Fin 3 → Fin 3 → Bounds :=
  fun i j => add (add (mul s (A i 0) (B 0 j)) (mul s (A i 1) (B 1 j))) (mul s (A i 2) (B 2 j))

theorem matrixMul3_mem {s : ℤ} (hs : 0<s) (IA IB : Fin 3 → Fin 3 → Bounds)
    (A B : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ∀ i j, Mem s (IA i j) (A i j)) (hB : ∀ i j, Mem s (IB i j) (B i j))
    (i j : Fin 3) : Mem s (matrixMul3 s IA IB i j) ((A*B) i j) := by
  simpa only [matrixMul3,Matrix.mul_apply,Fin.sum_univ_three] using
    mem_add (mem_add (mem_mul hs (hA i 0) (hB 0 j)) (mem_mul hs (hA i 1) (hB 1 j)))
      (mem_mul hs (hA i 2) (hB 2 j))
end ThomsonNine.FixedInterval
