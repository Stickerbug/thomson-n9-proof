import MainCoverage.RootSourceData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain.RootSource
open ThomsonNine.PackedTensor
theorem sorted_groups : FiniteCollector.sortFuel 11 ((List.finRange 757).flatMap groups)=List.range 1331 := by decide +kernel
theorem zero_fields : zeroIndices.all (fun id => decide (RootTensor.K00.coeff0 (unflat 11 id)=0))=true := by decide +kernel
theorem unflat_flat : ∀ p : CubeIndex 11, unflat 11 (flat p)=p := by decide +kernel
theorem flat_unflat : ∀ i : Fin 1331, flat (unflat 11 i.val)=i.val := by decide +kernel
end ThomsonNine.PackedMain.RootSource
