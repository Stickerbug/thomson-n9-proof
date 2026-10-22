import MainCoverage.AxisFields009
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_9 : ∀ i : Fin 32, AxisActualLower (axisLookup (288+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds009 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses009 i) (axisDiagIds009 i) (hb i)
    (axis_diag_fields_9 i).1 (axis_diag_fields_9 i).2 (axis_fields_9 i)
end ThomsonNine.PackedMain
