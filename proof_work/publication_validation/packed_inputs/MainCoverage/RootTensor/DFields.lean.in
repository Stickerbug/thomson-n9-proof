import MainCoverage.RootTensor.DData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain.RootTensor.D
open scoped BigOperators
open ThomsonNine.PackedTensor ThomsonNine.PackedRadix
theorem stage_fields : ∀ i : Fin 21, coeff1 i=∑ j, root20Int i j*coeff0 j := by decide +kernel
theorem source_fields : ∀ i : Fin 21, (coeff0 i : ℚ)/(denominator0 : ℚ)= -MainEnvelope.Archive.diagonalCoeff i := by decide +kernel
theorem lower_fields : ∀ i : Fin 21,
    ((limb 128 diagonalRootWord i.val : ℤ)-(offset : ℤ))*(denominator1 : ℤ)≤(scale : ℤ)*coeff1 i := by decide +kernel
theorem denominator_fields : denominator1=root20Den*denominator0 ∧ 0<denominator1 := by decide +kernel
end ThomsonNine.PackedMain.RootTensor.D
