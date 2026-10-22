import MainCoverage.AxisFields128
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_128 : ∀ i : Fin 32, AxisActualLower (axisLookup (4096+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds128 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses128 i) (axisDiagIds128 i) (hb i)
    (axis_diag_fields_128 i).1 (axis_diag_fields_128 i).2 (axis_fields_128 i)
end ThomsonNine.PackedMain
