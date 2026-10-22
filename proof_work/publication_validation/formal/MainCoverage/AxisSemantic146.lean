import MainCoverage.AxisFields146
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_146 : ∀ i : Fin 32, AxisActualLower (axisLookup (4672+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds146 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses146 i) (axisDiagIds146 i) (hb i)
    (axis_diag_fields_146 i).1 (axis_diag_fields_146 i).2 (axis_fields_146 i)
end ThomsonNine.PackedMain
