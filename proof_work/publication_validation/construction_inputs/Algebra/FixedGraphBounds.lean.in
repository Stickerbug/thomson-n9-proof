import ThomsonNine.Construction.Algebra.FixedMatrix
import ThomsonNine.Construction.Algebra.GramGraph
import ThomsonNine.Construction.Algebra.SchurCertificate
import ThomsonNine.IntervalSqrt

-- Isolated source: Algebra.FixedGraphBounds
noncomputable section
namespace ThomsonNine.FixedInterval
open scoped BigOperators

def matrixMulOver3 {m n : ℕ} (s : ℤ) (A : Fin m → Fin 3 → Bounds)
    (B : Fin 3 → Fin n → Bounds) : Fin m → Fin n → Bounds :=
  fun i j => add (add (mul s (A i 0) (B 0 j)) (mul s (A i 1) (B 1 j))) (mul s (A i 2) (B 2 j))
theorem matrixMulOver3_mem {m n : ℕ} {s : ℤ} (hs : 0<s)
    (IA : Fin m → Fin 3 → Bounds) (IB : Fin 3 → Fin n → Bounds)
    (A : Matrix (Fin m) (Fin 3) ℝ) (B : Matrix (Fin 3) (Fin n) ℝ)
    (hA : ∀ i j, Mem s (IA i j) (A i j)) (hB : ∀ i j, Mem s (IB i j) (B i j))
    (i j) : Mem s (matrixMulOver3 s IA IB i j) ((A*B) i j) := by
  simpa only [matrixMulOver3,Matrix.mul_apply,Fin.sum_univ_three] using
    mem_add (mem_add (mem_mul hs (hA i 0) (hB 0 j)) (mem_mul hs (hA i 1) (hB 1 j)))
      (mem_mul hs (hA i 2) (hB 2 j))

theorem sqrt_mem {s : ℤ} (hs : 0<s) (I J : Bounds) (hx : Mem s I x)
    (hI : 0≤I.lo) (hJ : 0≤J.lo) (hJhi : 0≤J.hi) (hSqLo : J.lo^2≤s*I.lo) (hSqHi : s*I.hi≤J.hi^2) :
    Mem s J (Real.sqrt x) := by
  have hs' : (0 : ℝ)<s := by exact_mod_cast hs
  have hI' : (0 : ℝ)≤I.lo := by exact_mod_cast hI
  have hJ' : (0 : ℝ)≤J.lo := by exact_mod_cast hJ
  have hL : (J.lo : ℝ)^2≤(s : ℝ)*I.lo := by exact_mod_cast hSqLo
  have hH : (s : ℝ)*I.hi≤(J.hi : ℝ)^2 := by exact_mod_cast hSqHi
  have hx0 : 0≤x := (mul_nonneg_iff_of_pos_left hs').mp (hI'.trans hx.1)
  have hsq := Real.sq_sqrt hx0
  have hpos := mul_nonneg (le_of_lt hs') (Real.sqrt_nonneg x)
  have hlo := mul_le_mul_of_nonneg_left hx.1 (le_of_lt hs')
  have hhi := mul_le_mul_of_nonneg_left hx.2 (le_of_lt hs')
  have hjhi : (0 : ℝ)≤J.hi := by exact_mod_cast hJhi
  have hscale : ((s : ℝ)*Real.sqrt x)^2=(s : ℝ)*((s : ℝ)*x) := by
    rw [mul_pow,hsq]
    ring
  rw [← hscale] at hlo hhi
  constructor
  · exact (sq_le_sq₀ hJ' hpos).mp (hL.trans hlo)
  · exact (sq_le_sq₀ hpos hjhi).mp (hhi.trans hH)
end ThomsonNine.FixedInterval
