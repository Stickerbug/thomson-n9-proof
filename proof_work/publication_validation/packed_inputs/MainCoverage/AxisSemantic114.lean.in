import MainCoverage.AxisFields114
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_114 : ∀ i : Fin 32, AxisActualLower (axisLookup (3648+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds114 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses114 i) (axisDiagIds114 i) (hb i)
    (axis_diag_fields_114 i).1 (axis_diag_fields_114 i).2 (axis_fields_114 i)
end ThomsonNine.PackedMain
