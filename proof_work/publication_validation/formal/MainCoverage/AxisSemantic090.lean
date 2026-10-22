import MainCoverage.AxisFields090
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_90 : ∀ i : Fin 32, AxisActualLower (axisLookup (2880+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds090 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses090 i) (axisDiagIds090 i) (hb i)
    (axis_diag_fields_90 i).1 (axis_diag_fields_90 i).2 (axis_fields_90 i)
end ThomsonNine.PackedMain
