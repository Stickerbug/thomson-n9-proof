import MainCoverage.AxisFields049
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_49 : ∀ i : Fin 32, AxisActualLower (axisLookup (1568+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds049 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses049 i) (axisDiagIds049 i) (hb i)
    (axis_diag_fields_49 i).1 (axis_diag_fields_49 i).2 (axis_fields_49 i)
end ThomsonNine.PackedMain
