import MainCoverage.AxisFields070
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_70 : ∀ i : Fin 32, AxisActualLower (axisLookup (2240+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds070 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses070 i) (axisDiagIds070 i) (hb i)
    (axis_diag_fields_70 i).1 (axis_diag_fields_70 i).2 (axis_fields_70 i)
end ThomsonNine.PackedMain
