import MainCoverage.RootTensor.GData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain.RootTensor.G
open ThomsonNine.PackedTensor ThomsonNine.PackedRadix
theorem lower_fields : ∀ i j k : Fin 3,
    ((limb 128 rootState.gram (index 3 i j k) : ℤ)-(offset : ℤ))*(denominator3 : ℤ)≤(scale : ℤ)*coeff3 (i,j,k) := by decide +kernel
end ThomsonNine.PackedMain.RootTensor.G
