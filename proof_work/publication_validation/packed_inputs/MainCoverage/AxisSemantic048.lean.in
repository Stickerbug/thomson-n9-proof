import MainCoverage.AxisFields048
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_48 : ∀ i : Fin 32, AxisActualLower (axisLookup (1536+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds048 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses048 i) (axisDiagIds048 i) (hb i)
    (axis_diag_fields_48 i).1 (axis_diag_fields_48 i).2 (axis_fields_48 i)
end ThomsonNine.PackedMain
