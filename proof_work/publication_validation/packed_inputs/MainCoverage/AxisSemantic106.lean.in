import MainCoverage.AxisFields106
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_106 : ∀ i : Fin 32, AxisActualLower (axisLookup (3392+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds106 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses106 i) (axisDiagIds106 i) (hb i)
    (axis_diag_fields_106 i).1 (axis_diag_fields_106 i).2 (axis_fields_106 i)
end ThomsonNine.PackedMain
