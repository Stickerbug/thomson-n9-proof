import MainCoverage.AxisFields016
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_16 : ∀ i : Fin 32, AxisActualLower (axisLookup (512+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds016 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses016 i) (axisDiagIds016 i) (hb i)
    (axis_diag_fields_16 i).1 (axis_diag_fields_16 i).2 (axis_fields_16 i)
end ThomsonNine.PackedMain
