import MainCoverage.AxisFields061
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_61 : ∀ i : Fin 32, AxisActualLower (axisLookup (1952+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds061 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses061 i) (axisDiagIds061 i) (hb i)
    (axis_diag_fields_61 i).1 (axis_diag_fields_61 i).2 (axis_fields_61 i)
end ThomsonNine.PackedMain
