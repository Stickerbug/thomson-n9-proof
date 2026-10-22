import MainCoverage.AxisFields010
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_10 : ∀ i : Fin 32, AxisActualLower (axisLookup (320+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds010 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses010 i) (axisDiagIds010 i) (hb i)
    (axis_diag_fields_10 i).1 (axis_diag_fields_10 i).2 (axis_fields_10 i)
end ThomsonNine.PackedMain
