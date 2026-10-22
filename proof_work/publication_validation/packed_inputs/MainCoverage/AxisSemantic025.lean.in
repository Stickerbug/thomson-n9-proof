import MainCoverage.AxisFields025
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_25 : ∀ i : Fin 32, AxisActualLower (axisLookup (800+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds025 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses025 i) (axisDiagIds025 i) (hb i)
    (axis_diag_fields_25 i).1 (axis_diag_fields_25 i).2 (axis_fields_25 i)
end ThomsonNine.PackedMain
