import MainCoverage.AxisFields149
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_149 : ∀ i : Fin 32, AxisActualLower (axisLookup (4768+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds149 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses149 i) (axisDiagIds149 i) (hb i)
    (axis_diag_fields_149 i).1 (axis_diag_fields_149 i).2 (axis_fields_149 i)
end ThomsonNine.PackedMain
