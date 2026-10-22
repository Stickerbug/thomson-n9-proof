import MainCoverage.AxisFields091
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_91 : ∀ i : Fin 32, AxisActualLower (axisLookup (2912+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds091 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses091 i) (axisDiagIds091 i) (hb i)
    (axis_diag_fields_91 i).1 (axis_diag_fields_91 i).2 (axis_fields_91 i)
end ThomsonNine.PackedMain
