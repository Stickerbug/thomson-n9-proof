import MainCoverage.RootTensor.K00Data
import MainCoverage.RootTensor.K02Data
import MainCoverage.PenaltyData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
theorem source_relation_2 : ∀ i j k : Fin 11,
    (RootTensor.K02.coeff0 (i,j,k) : ℚ)/(RootTensor.K02.denominator0 : ℚ)=
      (RootTensor.K00.coeff0 (i,j,k) : ℚ)/(RootTensor.K00.denominator0 : ℚ)+penalty 2*(gramInput 11 (i,j,k) : ℚ) := by decide +kernel
end ThomsonNine.PackedMain
