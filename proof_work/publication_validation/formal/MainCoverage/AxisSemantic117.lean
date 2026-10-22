import MainCoverage.AxisFields117
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_117 : ∀ i : Fin 32, AxisActualLower (axisLookup (3744+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds117 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses117 i) (axisDiagIds117 i) (hb i)
    (axis_diag_fields_117 i).1 (axis_diag_fields_117 i).2 (axis_fields_117 i)
end ThomsonNine.PackedMain
