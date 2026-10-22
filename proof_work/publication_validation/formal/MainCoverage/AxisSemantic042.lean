import MainCoverage.AxisFields042
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_42 : ∀ i : Fin 32, AxisActualLower (axisLookup (1344+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds042 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses042 i) (axisDiagIds042 i) (hb i)
    (axis_diag_fields_42 i).1 (axis_diag_fields_42 i).2 (axis_fields_42 i)
end ThomsonNine.PackedMain
