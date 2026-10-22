import ThomsonNine.Construction.Kernel.SyzygyData

-- Isolated source: Kernel.Syzygy10
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualKernel.Syzygy
theorem p_zero_10 : ∀ i : Fin 11, dotNum p 10 i=[] := by decide +kernel
theorem c_zero_10 : ∀ i : Fin 11, dotNum c 10 i=[] := by decide +kernel
end ThomsonNine.ActualKernel.Syzygy
