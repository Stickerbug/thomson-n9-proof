import Kernel.QCacheData

noncomputable section
namespace ThomsonNine.ActualKernel.QCache
open ThomsonNine.ContactJet
open ThomsonNine.ActualHermite.CoefficientData

theorem inputValue_mem (p : Fin 19) (σ : Fin 6) (n : ℕ) (hn : n≤10) :
    Mem unitScale (inputValue p σ n) (q (U p σ) (V p σ) (T p σ) n) := by
  have hu : Mem unitScale (IU p σ) (U p σ) := mem_coordinate (point_mem p) _
  have hv : Mem unitScale (IV p σ) (V p σ) := mem_coordinate (point_mem p) _
  have ht : Mem unitScale (IT p σ) (T p σ) := mem_coordinate (point_mem p) _
  have hc1 : Mem unitScale (inputConstant (FixedInterval.constant unitScale 1)) (constant 1) := by
    simpa using mem_constant (FixedInterval.mem_constant unitScale 1)
  have hc2 : Mem unitScale (inputConstant (FixedInterval.constant unitScale 2)) (constant 2) := by
    simpa using mem_constant (FixedInterval.mem_constant unitScale 2)
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact mem_contains (zero_bounds p σ) hc1
    | succ n =>
      cases n with
      | zero => exact mem_contains (one_bounds p σ) (mem_subtract ht (mem_mul unitScale_pos hu hv))
      | succ k =>
        have h0 := ih k (by omega) (by omega)
        have h1 := ih (k+1) (by omega) (by omega)
        apply mem_contains (step_bounds p σ ⟨k,by omega⟩)
        exact mem_subtract
          (mem_mul unitScale_pos (mem_mul unitScale_pos hc2 (mem_subtract ht (mem_mul unitScale_pos hu hv))) h1)
          (mem_mul unitScale_pos (mem_mul unitScale_pos (mem_subtract hc1 (mem_mul unitScale_pos hu hu))
            (mem_subtract hc1 (mem_mul unitScale_pos hv hv))) h0)
end ThomsonNine.ActualKernel.QCache
