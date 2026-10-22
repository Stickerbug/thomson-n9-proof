import MainCoverage.AxisFields079
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_79 : ∀ i : Fin 32, AxisActualLower (axisLookup (2528+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds079 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses079 i) (axisDiagIds079 i) (hb i)
    (axis_diag_fields_79 i).1 (axis_diag_fields_79 i).2 (axis_fields_79 i)
end ThomsonNine.PackedMain
