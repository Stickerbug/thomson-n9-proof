import MainCoverage.AxisFields120
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_120 : ∀ i : Fin 32, AxisActualLower (axisLookup (3840+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds120 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses120 i) (axisDiagIds120 i) (hb i)
    (axis_diag_fields_120 i).1 (axis_diag_fields_120 i).2 (axis_fields_120 i)
end ThomsonNine.PackedMain
