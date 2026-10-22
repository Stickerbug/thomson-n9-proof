import MainCoverage.AxisFields054
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_54 : ∀ i : Fin 32, AxisActualLower (axisLookup (1728+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds054 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses054 i) (axisDiagIds054 i) (hb i)
    (axis_diag_fields_54 i).1 (axis_diag_fields_54 i).2 (axis_fields_54 i)
end ThomsonNine.PackedMain
