import ThomsonNine.AAAGroupedData

/-! End-to-end pilot of the uniform grouping theorem and ordinary kernel
reduction. t000 has all 807 archived source terms as contributors. These are
conditional coefficient enclosures, not exact contact or residual identities. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
noncomputable section
namespace ThomsonNine.AAAGroupedPilot
open ThomsonNine.LocalSparseHessianAAA ThomsonNine.AAAGroupedData
open ThomsonNine.GatheredBinding

/-- A smaller two-axis regression case for the uniform numeric evaluator. -/
theorem bounds286 :
    (coefficientInterval .t286).lo ≤ (computed .t286).lo ∧
    (computed .t286).hi ≤ (coefficientInterval .t286).hi := by
  decide +kernel

/-- The constant target includes all 807 sources, rather than a small fiber. -/
theorem bounds000 :
    (coefficientInterval .t000).lo ≤ (computed .t000).lo ∧
    (computed .t000).hi ≤ (coefficientInterval .t000).hi := by
  decide +kernel

/-- One hard target is closed by the generic theorem and checked endpoints.
The coefficient family and center are fixed for the whole gathered expression. -/
theorem t000_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t))
    (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t000).mem (gathered (exponents .t000) c a) := by
  exact gathered_mem_of_bounds c a hC ha .t000 bounds000.1 bounds000.2

end ThomsonNine.AAAGroupedPilot
