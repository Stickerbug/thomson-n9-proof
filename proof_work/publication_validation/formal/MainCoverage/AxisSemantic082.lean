import MainCoverage.AxisFields082
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_82 : ∀ i : Fin 32, AxisActualLower (axisLookup (2624+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds082 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses082 i) (axisDiagIds082 i) (hb i)
    (axis_diag_fields_82 i).1 (axis_diag_fields_82 i).2 (axis_fields_82 i)
end ThomsonNine.PackedMain
