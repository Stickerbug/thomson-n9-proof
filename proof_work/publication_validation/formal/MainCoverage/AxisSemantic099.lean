import MainCoverage.AxisFields099
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_99 : ∀ i : Fin 32, AxisActualLower (axisLookup (3168+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds099 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses099 i) (axisDiagIds099 i) (hb i)
    (axis_diag_fields_99 i).1 (axis_diag_fields_99 i).2 (axis_fields_99 i)
end ThomsonNine.PackedMain
