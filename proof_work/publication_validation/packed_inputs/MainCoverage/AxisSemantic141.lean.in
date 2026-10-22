import MainCoverage.AxisFields141
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_141 : ∀ i : Fin 32, AxisActualLower (axisLookup (4512+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds141 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses141 i) (axisDiagIds141 i) (hb i)
    (axis_diag_fields_141 i).1 (axis_diag_fields_141 i).2 (axis_fields_141 i)
end ThomsonNine.PackedMain
