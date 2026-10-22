import MainCoverage.AxisFields026
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_26 : ∀ i : Fin 32, AxisActualLower (axisLookup (832+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds026 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses026 i) (axisDiagIds026 i) (hb i)
    (axis_diag_fields_26 i).1 (axis_diag_fields_26 i).2 (axis_fields_26 i)
end ThomsonNine.PackedMain
