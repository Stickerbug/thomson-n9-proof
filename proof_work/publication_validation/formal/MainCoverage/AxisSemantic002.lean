import MainCoverage.AxisFields002
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_2 : ∀ i : Fin 32, AxisActualLower (axisLookup (64+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds002 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses002 i) (axisDiagIds002 i) (hb i)
    (axis_diag_fields_2 i).1 (axis_diag_fields_2 i).2 (axis_fields_2 i)
end ThomsonNine.PackedMain
