import MainCoverage.AxisFields112
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_112 : ∀ i : Fin 32, AxisActualLower (axisLookup (3584+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds112 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses112 i) (axisDiagIds112 i) (hb i)
    (axis_diag_fields_112 i).1 (axis_diag_fields_112 i).2 (axis_fields_112 i)
end ThomsonNine.PackedMain
