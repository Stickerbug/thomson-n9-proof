import MainCoverage.RootTensor.K00Data
import MainCoverage.RootTensor.K01Data
import MainCoverage.PenaltyData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
theorem source_relation_1 : ∀ i j k : Fin 11,
    (RootTensor.K01.coeff0 (i,j,k) : ℚ)/(RootTensor.K01.denominator0 : ℚ)=
      (RootTensor.K00.coeff0 (i,j,k) : ℚ)/(RootTensor.K00.denominator0 : ℚ)+penalty 1*(gramInput 11 (i,j,k) : ℚ) := by decide +kernel
end ThomsonNine.PackedMain
