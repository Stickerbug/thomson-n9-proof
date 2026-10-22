import MainCoverage.AxisFields132
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_132 : ∀ i : Fin 32, AxisActualLower (axisLookup (4224+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds132 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses132 i) (axisDiagIds132 i) (hb i)
    (axis_diag_fields_132 i).1 (axis_diag_fields_132 i).2 (axis_fields_132 i)
end ThomsonNine.PackedMain
