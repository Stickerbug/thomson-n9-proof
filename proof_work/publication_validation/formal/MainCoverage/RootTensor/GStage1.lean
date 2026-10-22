import MainCoverage.RootTensor.GData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain.RootTensor.G
open ThomsonNine.PackedTensor
theorem stage1_fields : ∀ i j k : Fin 3, coeff1 (i,j,k)=mapAxisInt root02Int 0 coeff0 (i,j,k) := by decide +kernel
end ThomsonNine.PackedMain.RootTensor.G
