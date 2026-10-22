import MainCoverage.AxisFields084
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_84 : ∀ i : Fin 32, AxisActualLower (axisLookup (2688+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds084 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses084 i) (axisDiagIds084 i) (hb i)
    (axis_diag_fields_84 i).1 (axis_diag_fields_84 i).2 (axis_fields_84 i)
end ThomsonNine.PackedMain
