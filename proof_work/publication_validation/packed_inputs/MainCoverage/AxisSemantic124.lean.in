import MainCoverage.AxisFields124
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_124 : ∀ i : Fin 32, AxisActualLower (axisLookup (3968+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds124 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses124 i) (axisDiagIds124 i) (hb i)
    (axis_diag_fields_124 i).1 (axis_diag_fields_124 i).2 (axis_fields_124 i)
end ThomsonNine.PackedMain
