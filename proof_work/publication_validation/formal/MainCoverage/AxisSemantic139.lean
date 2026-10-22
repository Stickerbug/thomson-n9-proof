import MainCoverage.AxisFields139
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_139 : ∀ i : Fin 32, AxisActualLower (axisLookup (4448+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds139 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses139 i) (axisDiagIds139 i) (hb i)
    (axis_diag_fields_139 i).1 (axis_diag_fields_139 i).2 (axis_fields_139 i)
end ThomsonNine.PackedMain
