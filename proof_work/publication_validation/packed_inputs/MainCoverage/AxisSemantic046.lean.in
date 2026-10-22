import MainCoverage.AxisFields046
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_46 : ∀ i : Fin 32, AxisActualLower (axisLookup (1472+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds046 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses046 i) (axisDiagIds046 i) (hb i)
    (axis_diag_fields_46 i).1 (axis_diag_fields_46 i).2 (axis_fields_46 i)
end ThomsonNine.PackedMain
