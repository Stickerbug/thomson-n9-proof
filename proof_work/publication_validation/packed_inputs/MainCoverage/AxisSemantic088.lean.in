import MainCoverage.AxisFields088
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_88 : ∀ i : Fin 32, AxisActualLower (axisLookup (2816+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds088 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses088 i) (axisDiagIds088 i) (hb i)
    (axis_diag_fields_88 i).1 (axis_diag_fields_88 i).2 (axis_fields_88 i)
end ThomsonNine.PackedMain
