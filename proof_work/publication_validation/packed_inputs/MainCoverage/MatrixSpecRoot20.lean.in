import MainCoverage.AffineData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
open ThomsonNine.PackedTensor
theorem root20_spec : affineMatrixSpec 20 root20 (-1/1 : ℚ) (39/25 : ℚ) := by decide +kernel
theorem root20_fields : ∀ i j : Fin 21, root20 i j=(root20Int i j : ℚ)/(root20Den : ℚ) := by decide +kernel
end ThomsonNine.PackedMain
