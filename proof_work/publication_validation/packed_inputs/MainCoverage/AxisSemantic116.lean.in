import MainCoverage.AxisFields116
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_116 : ∀ i : Fin 32, AxisActualLower (axisLookup (3712+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds116 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses116 i) (axisDiagIds116 i) (hb i)
    (axis_diag_fields_116 i).1 (axis_diag_fields_116 i).2 (axis_fields_116 i)
end ThomsonNine.PackedMain
