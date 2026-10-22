import MainCoverage.AxisFields064
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_64 : ∀ i : Fin 32, AxisActualLower (axisLookup (2048+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds064 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses064 i) (axisDiagIds064 i) (hb i)
    (axis_diag_fields_64 i).1 (axis_diag_fields_64 i).2 (axis_fields_64 i)
end ThomsonNine.PackedMain
