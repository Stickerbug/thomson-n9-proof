import MainCoverage.AxisFields011
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_11 : ∀ i : Fin 32, AxisActualLower (axisLookup (352+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds011 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses011 i) (axisDiagIds011 i) (hb i)
    (axis_diag_fields_11 i).1 (axis_diag_fields_11 i).2 (axis_fields_11 i)
end ThomsonNine.PackedMain
