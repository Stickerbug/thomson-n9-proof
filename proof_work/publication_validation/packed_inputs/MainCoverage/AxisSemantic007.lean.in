import MainCoverage.AxisFields007
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_7 : ∀ i : Fin 32, AxisActualLower (axisLookup (224+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds007 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses007 i) (axisDiagIds007 i) (hb i)
    (axis_diag_fields_7 i).1 (axis_diag_fields_7 i).2 (axis_fields_7 i)
end ThomsonNine.PackedMain
