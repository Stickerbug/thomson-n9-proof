import MainCoverage.AxisFields085
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_85 : ∀ i : Fin 32, AxisActualLower (axisLookup (2720+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds085 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses085 i) (axisDiagIds085 i) (hb i)
    (axis_diag_fields_85 i).1 (axis_diag_fields_85 i).2 (axis_fields_85 i)
end ThomsonNine.PackedMain
