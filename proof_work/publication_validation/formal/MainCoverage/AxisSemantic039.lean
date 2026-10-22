import MainCoverage.AxisFields039
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_39 : ∀ i : Fin 32, AxisActualLower (axisLookup (1248+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds039 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses039 i) (axisDiagIds039 i) (hb i)
    (axis_diag_fields_39 i).1 (axis_diag_fields_39 i).2 (axis_fields_39 i)
end ThomsonNine.PackedMain
