import MainCoverage.AxisFields122
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_122 : ∀ i : Fin 32, AxisActualLower (axisLookup (3904+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds122 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses122 i) (axisDiagIds122 i) (hb i)
    (axis_diag_fields_122 i).1 (axis_diag_fields_122 i).2 (axis_fields_122 i)
end ThomsonNine.PackedMain
