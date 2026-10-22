import MainCoverage.AxisFields081
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_81 : ∀ i : Fin 32, AxisActualLower (axisLookup (2592+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds081 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses081 i) (axisDiagIds081 i) (hb i)
    (axis_diag_fields_81 i).1 (axis_diag_fields_81 i).2 (axis_fields_81 i)
end ThomsonNine.PackedMain
