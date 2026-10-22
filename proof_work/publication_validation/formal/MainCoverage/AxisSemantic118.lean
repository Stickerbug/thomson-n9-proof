import MainCoverage.AxisFields118
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_118 : ∀ i : Fin 32, AxisActualLower (axisLookup (3776+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds118 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses118 i) (axisDiagIds118 i) (hb i)
    (axis_diag_fields_118 i).1 (axis_diag_fields_118 i).2 (axis_fields_118 i)
end ThomsonNine.PackedMain
