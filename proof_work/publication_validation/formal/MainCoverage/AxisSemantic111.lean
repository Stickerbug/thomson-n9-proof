import MainCoverage.AxisFields111
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_111 : ∀ i : Fin 32, AxisActualLower (axisLookup (3552+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds111 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses111 i) (axisDiagIds111 i) (hb i)
    (axis_diag_fields_111 i).1 (axis_diag_fields_111 i).2 (axis_fields_111 i)
end ThomsonNine.PackedMain
