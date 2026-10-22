import ThomsonNine.Construction.Kernel.CachedData

-- Isolated source: Kernel.Data
noncomputable section
namespace ThomsonNine.ActualKernel
open ThomsonNine.FixedInterval
open ThomsonNine.ActualHermite.CoefficientData
theorem inputN_eq_cached (k i j : Fin 11) : inputN k i j=cachedN k i j :=
  congrArg₂ Bounds.mk (inputN_cached_fields k i j).1 (inputN_cached_fields k i j).2
theorem cachedN_mem (k i j : Fin 11) : Mem unitScale (cachedN k i j) (N k i j) := by
  rw [← inputN_eq_cached]
  exact inputN_mem k i j

theorem inputN_bounds : ∀ k i j : Fin 11,
    (unitScale : ℚ)*(archiveInterval k i j).lo ≤ ((cachedN k i j).lo : ℚ) ∧
    ((cachedN k i j).hi : ℚ) ≤ (unitScale : ℚ)*(archiveInterval k i j).hi := by decide +kernel
theorem N_mem_archive (k i j : Fin 11) : (archiveInterval k i j).mem (N k i j) :=
  mem_to_rat (cachedN_mem k i j) unitScale_pos (inputN_bounds k i j).1 (inputN_bounds k i j).2
end ThomsonNine.ActualKernel
