import MainCoverage.AxisFields097
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_97 : ∀ i : Fin 32, AxisActualLower (axisLookup (3104+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds097 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses097 i) (axisDiagIds097 i) (hb i)
    (axis_diag_fields_97 i).1 (axis_diag_fields_97 i).2 (axis_fields_97 i)
end ThomsonNine.PackedMain
