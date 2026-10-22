import MainCoverage.AxisFields035
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_35 : ∀ i : Fin 32, AxisActualLower (axisLookup (1120+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds035 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses035 i) (axisDiagIds035 i) (hb i)
    (axis_diag_fields_35 i).1 (axis_diag_fields_35 i).2 (axis_fields_35 i)
end ThomsonNine.PackedMain
