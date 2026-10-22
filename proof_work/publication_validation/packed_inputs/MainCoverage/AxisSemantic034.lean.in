import MainCoverage.AxisFields034
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_34 : ∀ i : Fin 32, AxisActualLower (axisLookup (1088+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds034 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses034 i) (axisDiagIds034 i) (hb i)
    (axis_diag_fields_34 i).1 (axis_diag_fields_34 i).2 (axis_fields_34 i)
end ThomsonNine.PackedMain
