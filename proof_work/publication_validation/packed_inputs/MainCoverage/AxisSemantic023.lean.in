import MainCoverage.AxisFields023
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_23 : ∀ i : Fin 32, AxisActualLower (axisLookup (736+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds023 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses023 i) (axisDiagIds023 i) (hb i)
    (axis_diag_fields_23 i).1 (axis_diag_fields_23 i).2 (axis_fields_23 i)
end ThomsonNine.PackedMain
