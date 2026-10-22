import MainCoverage.AxisFields005
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_5 : ∀ i : Fin 32, AxisActualLower (axisLookup (160+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds005 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses005 i) (axisDiagIds005 i) (hb i)
    (axis_diag_fields_5 i).1 (axis_diag_fields_5 i).2 (axis_fields_5 i)
end ThomsonNine.PackedMain
