import MainCoverage.AxisFields020
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_20 : ∀ i : Fin 32, AxisActualLower (axisLookup (640+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds020 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses020 i) (axisDiagIds020 i) (hb i)
    (axis_diag_fields_20 i).1 (axis_diag_fields_20 i).2 (axis_fields_20 i)
end ThomsonNine.PackedMain
