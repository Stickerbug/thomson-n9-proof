import MainCoverage.AxisFields065
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_65 : ∀ i : Fin 32, AxisActualLower (axisLookup (2080+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds065 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses065 i) (axisDiagIds065 i) (hb i)
    (axis_diag_fields_65 i).1 (axis_diag_fields_65 i).2 (axis_fields_65 i)
end ThomsonNine.PackedMain
