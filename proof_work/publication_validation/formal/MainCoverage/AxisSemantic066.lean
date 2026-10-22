import MainCoverage.AxisFields066
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_66 : ∀ i : Fin 32, AxisActualLower (axisLookup (2112+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds066 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses066 i) (axisDiagIds066 i) (hb i)
    (axis_diag_fields_66 i).1 (axis_diag_fields_66 i).2 (axis_fields_66 i)
end ThomsonNine.PackedMain
