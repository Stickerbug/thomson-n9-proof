import ThomsonNine.RefinedRadius
import ThomsonNine.AAACollected

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
noncomputable section
namespace ThomsonNine.RefinedRadius
open ThomsonNine.Interval ThomsonNine.Interval.RatInterval
open ThomsonNine.Interval.SparsePolynomial
open ThomsonNine.AAAGroupedData ThomsonNine.LocalSparseHessianAAA

/-- The AAA contact center is determined by the actual stationary radius. -/
def aaaCenter (_ : Fin 3) : ℝ := 1-3*radius^2/2

def centerComputed : RatInterval :=
  sub (const 1) (mul (mul enclosure enclosure) (const (3/2)))

theorem centerComputed_mem : centerComputed.mem (1-3*radius^2/2) := by
  have h := mem_sub (mem_const 1) (mem_mul (mem_mul radius_mem radius_mem) (mem_const (3/2)))
  convert h using 1 <;> first | rfl | (norm_num [pow_two, div_eq_mul_inv]; try ring)

theorem center_bounds : ∀ i : Fin 3,
    (centerInterval i).lo ≤ centerComputed.lo ∧ centerComputed.hi ≤ (centerInterval i).hi := by
  decide +kernel

theorem aaaCenter_mem : ∀ i : Fin 3, (centerInterval i).mem (aaaCenter i) := by
  intro i
  exact mem_subset centerComputed_mem (center_bounds i).1 (center_bounds i).2

theorem source_h00_at_actual_center (c : TermIndex → ℝ) (x : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t))
    (hx : ∀ i, (relativeBox i).mem (x i)) :
    targetH00.mem
      (axisDeriv (axisDeriv (fun y => eval exponents c y GatheredBinding.allTerms) 0) 0
        (fun i => aaaCenter i+x i)) :=
  AAACollected.source_h00_mem c aaaCenter x hC aaaCenter_mem hx
end ThomsonNine.RefinedRadius
