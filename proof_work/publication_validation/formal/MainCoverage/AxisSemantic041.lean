import MainCoverage.AxisFields041
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_41 : ∀ i : Fin 32, AxisActualLower (axisLookup (1312+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds041 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses041 i) (axisDiagIds041 i) (hb i)
    (axis_diag_fields_41 i).1 (axis_diag_fields_41 i).2 (axis_fields_41 i)
end ThomsonNine.PackedMain
