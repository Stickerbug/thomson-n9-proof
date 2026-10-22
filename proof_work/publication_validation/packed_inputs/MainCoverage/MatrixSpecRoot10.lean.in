import MainCoverage.AffineData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
open ThomsonNine.PackedTensor
theorem root10_spec : affineMatrixSpec 10 root10 (-1/1 : ℚ) (39/25 : ℚ) := by decide +kernel
theorem root10_fields : ∀ i j : Fin 11, root10 i j=(root10Int i j : ℚ)/(root10Den : ℚ) := by decide +kernel
end ThomsonNine.PackedMain
