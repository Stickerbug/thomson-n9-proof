import MainCoverage.AxisFields000
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_0 : ∀ i : Fin 32, AxisActualLower (axisLookup (0+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds000 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses000 i) (axisDiagIds000 i) (hb i)
    (axis_diag_fields_0 i).1 (axis_diag_fields_0 i).2 (axis_fields_0 i)
end ThomsonNine.PackedMain
