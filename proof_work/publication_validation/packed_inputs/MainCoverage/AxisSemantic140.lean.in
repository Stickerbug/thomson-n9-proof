import MainCoverage.AxisFields140
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_140 : ∀ i : Fin 32, AxisActualLower (axisLookup (4480+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds140 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses140 i) (axisDiagIds140 i) (hb i)
    (axis_diag_fields_140 i).1 (axis_diag_fields_140 i).2 (axis_fields_140 i)
end ThomsonNine.PackedMain
