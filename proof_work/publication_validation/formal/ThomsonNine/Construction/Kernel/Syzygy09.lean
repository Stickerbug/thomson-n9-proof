import ThomsonNine.Construction.Kernel.SyzygyData

-- Isolated source: Kernel.Syzygy09
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualKernel.Syzygy
theorem p_zero_09 : ∀ i : Fin 11, dotNum p 9 i=[] := by decide +kernel
theorem c_zero_09 : ∀ i : Fin 11, dotNum c 9 i=[] := by decide +kernel
end ThomsonNine.ActualKernel.Syzygy
