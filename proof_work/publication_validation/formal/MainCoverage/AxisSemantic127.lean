import MainCoverage.AxisFields127
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_127 : ∀ i : Fin 32, AxisActualLower (axisLookup (4064+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds127 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses127 i) (axisDiagIds127 i) (hb i)
    (axis_diag_fields_127 i).1 (axis_diag_fields_127 i).2 (axis_fields_127 i)
end ThomsonNine.PackedMain
