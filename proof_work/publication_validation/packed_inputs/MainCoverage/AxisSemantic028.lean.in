import MainCoverage.AxisFields028
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_28 : ∀ i : Fin 32, AxisActualLower (axisLookup (896+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds028 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses028 i) (axisDiagIds028 i) (hb i)
    (axis_diag_fields_28 i).1 (axis_diag_fields_28 i).2 (axis_fields_28 i)
end ThomsonNine.PackedMain
