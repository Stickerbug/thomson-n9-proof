import MainCoverage.AxisFields123
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_123 : ∀ i : Fin 32, AxisActualLower (axisLookup (3936+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds123 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses123 i) (axisDiagIds123 i) (hb i)
    (axis_diag_fields_123 i).1 (axis_diag_fields_123 i).2 (axis_fields_123 i)
end ThomsonNine.PackedMain
