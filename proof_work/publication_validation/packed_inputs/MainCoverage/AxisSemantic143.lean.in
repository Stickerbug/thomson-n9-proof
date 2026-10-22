import MainCoverage.AxisFields143
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_143 : ∀ i : Fin 32, AxisActualLower (axisLookup (4576+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds143 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses143 i) (axisDiagIds143 i) (hb i)
    (axis_diag_fields_143 i).1 (axis_diag_fields_143 i).2 (axis_fields_143 i)
end ThomsonNine.PackedMain
