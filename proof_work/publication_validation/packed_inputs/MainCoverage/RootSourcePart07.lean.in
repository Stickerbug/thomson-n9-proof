import MainCoverage.RootSourceData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain.RootSource
open ThomsonNine.PackedTensor
theorem source_fields_7 : ∀ i : Fin 64,
    let j := Fin.ofNat 756 (448+i.val)
    (RootTensor.K00.coeff0 (unflat 11 (sourceIndex j)) : ℚ)/(RootTensor.K00.denominator0 : ℚ)=MainEnvelope.Archive.kernelCoeff j ∧
      ∀ a : Fin 3, (coord a (unflat 11 (sourceIndex j))).val=ActualF.Data.support j a := by decide +kernel
end ThomsonNine.PackedMain.RootSource
