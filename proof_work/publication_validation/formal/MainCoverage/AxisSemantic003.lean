import MainCoverage.AxisFields003
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_3 : ∀ i : Fin 32, AxisActualLower (axisLookup (96+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds003 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses003 i) (axisDiagIds003 i) (hb i)
    (axis_diag_fields_3 i).1 (axis_diag_fields_3 i).2 (axis_fields_3 i)
end ThomsonNine.PackedMain
