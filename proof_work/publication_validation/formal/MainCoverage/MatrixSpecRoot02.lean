import MainCoverage.AffineData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
open ThomsonNine.PackedTensor
theorem root02_spec : affineMatrixSpec 2 root02 (-1/1 : ℚ) (39/25 : ℚ) := by decide +kernel
theorem root02_fields : ∀ i j : Fin 3, root02 i j=(root02Int i j : ℚ)/(root02Den : ℚ) := by decide +kernel
end ThomsonNine.PackedMain
