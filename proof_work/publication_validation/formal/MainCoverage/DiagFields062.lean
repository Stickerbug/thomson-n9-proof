import MainCoverage.DiagonalData
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
namespace ThomsonNine.PackedMain
theorem diagonal_fields_62 : ∀ i : Fin 64, diagonalOK diagonalLookup diagonalRootWord (3968+i.val)=true := by decide +kernel
end ThomsonNine.PackedMain
