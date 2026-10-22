import MainCoverage.AxisFields017
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_17 : ∀ i : Fin 32, AxisActualLower (axisLookup (544+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds017 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses017 i) (axisDiagIds017 i) (hb i)
    (axis_diag_fields_17 i).1 (axis_diag_fields_17 i).2 (axis_fields_17 i)
end ThomsonNine.PackedMain
