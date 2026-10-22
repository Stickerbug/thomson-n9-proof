import MainCoverage.AxisFields015
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_15 : ∀ i : Fin 32, AxisActualLower (axisLookup (480+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds015 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses015 i) (axisDiagIds015 i) (hb i)
    (axis_diag_fields_15 i).1 (axis_diag_fields_15 i).2 (axis_fields_15 i)
end ThomsonNine.PackedMain
