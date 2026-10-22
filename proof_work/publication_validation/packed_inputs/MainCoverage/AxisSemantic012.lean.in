import MainCoverage.AxisFields012
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_12 : ∀ i : Fin 32, AxisActualLower (axisLookup (384+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds012 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses012 i) (axisDiagIds012 i) (hb i)
    (axis_diag_fields_12 i).1 (axis_diag_fields_12 i).2 (axis_fields_12 i)
end ThomsonNine.PackedMain
