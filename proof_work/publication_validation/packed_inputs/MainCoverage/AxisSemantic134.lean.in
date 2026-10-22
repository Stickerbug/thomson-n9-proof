import MainCoverage.AxisFields134
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_134 : ∀ i : Fin 32, AxisActualLower (axisLookup (4288+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds134 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses134 i) (axisDiagIds134 i) (hb i)
    (axis_diag_fields_134 i).1 (axis_diag_fields_134 i).2 (axis_fields_134 i)
end ThomsonNine.PackedMain
