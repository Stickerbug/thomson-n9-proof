import MainCoverage.AxisFields150
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_150 : ∀ i : Fin 10, AxisActualLower (axisLookup (4800+i.val)) := by
  have hb : ∀ i : Fin 10, axisDiagIds150 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses150 i) (axisDiagIds150 i) (hb i)
    (axis_diag_fields_150 i).1 (axis_diag_fields_150 i).2 (axis_fields_150 i)
end ThomsonNine.PackedMain
