import MainCoverage.RootTensor.K01Data
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain.RootTensor.K01
open ThomsonNine.PackedTensor ThomsonNine.PackedRadix
theorem lower_fields : ∀ i j k : Fin 11,
    ((limb 128 (rootState.kernels 1) (index 11 i j k) : ℤ)-(offset : ℤ))*(denominator3 : ℤ)≤(scale : ℤ)*coeff3 (i,j,k) := by decide +kernel
end ThomsonNine.PackedMain.RootTensor.K01
