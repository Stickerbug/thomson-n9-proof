import MainCoverage.AxisFields018
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_18 : ∀ i : Fin 32, AxisActualLower (axisLookup (576+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds018 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses018 i) (axisDiagIds018 i) (hb i)
    (axis_diag_fields_18 i).1 (axis_diag_fields_18 i).2 (axis_fields_18 i)
end ThomsonNine.PackedMain
