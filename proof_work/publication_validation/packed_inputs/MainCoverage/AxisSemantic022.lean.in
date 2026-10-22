import MainCoverage.AxisFields022
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_22 : ∀ i : Fin 32, AxisActualLower (axisLookup (704+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds022 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses022 i) (axisDiagIds022 i) (hb i)
    (axis_diag_fields_22 i).1 (axis_diag_fields_22 i).2 (axis_fields_22 i)
end ThomsonNine.PackedMain
