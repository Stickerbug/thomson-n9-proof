import MainCoverage.AxisFields033
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_33 : ∀ i : Fin 32, AxisActualLower (axisLookup (1056+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds033 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses033 i) (axisDiagIds033 i) (hb i)
    (axis_diag_fields_33 i).1 (axis_diag_fields_33 i).2 (axis_fields_33 i)
end ThomsonNine.PackedMain
