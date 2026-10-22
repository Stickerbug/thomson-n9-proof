import MainCoverage.AxisFields021
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_21 : ∀ i : Fin 32, AxisActualLower (axisLookup (672+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds021 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses021 i) (axisDiagIds021 i) (hb i)
    (axis_diag_fields_21 i).1 (axis_diag_fields_21 i).2 (axis_fields_21 i)
end ThomsonNine.PackedMain
