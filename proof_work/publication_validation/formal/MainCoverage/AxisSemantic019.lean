import MainCoverage.AxisFields019
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_19 : ∀ i : Fin 32, AxisActualLower (axisLookup (608+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds019 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses019 i) (axisDiagIds019 i) (hb i)
    (axis_diag_fields_19 i).1 (axis_diag_fields_19 i).2 (axis_fields_19 i)
end ThomsonNine.PackedMain
