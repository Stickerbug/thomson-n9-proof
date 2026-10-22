import MainCoverage.RootTensor.GData
import MainCoverage.GramInput
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem gram_source_fields : ∀ i j k : Fin 3,
    (RootTensor.G.coeff0 (i,j,k) : ℚ)/(RootTensor.G.denominator0 : ℚ)=(gramInput 3 (i,j,k) : ℚ) := by decide +kernel
end ThomsonNine.PackedMain
