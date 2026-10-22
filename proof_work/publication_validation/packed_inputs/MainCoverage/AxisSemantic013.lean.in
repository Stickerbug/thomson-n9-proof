import MainCoverage.AxisFields013
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_13 : ∀ i : Fin 32, AxisActualLower (axisLookup (416+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds013 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses013 i) (axisDiagIds013 i) (hb i)
    (axis_diag_fields_13 i).1 (axis_diag_fields_13 i).2 (axis_fields_13 i)
end ThomsonNine.PackedMain
