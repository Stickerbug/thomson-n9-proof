import MainCoverage.AxisFields004
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_4 : ∀ i : Fin 32, AxisActualLower (axisLookup (128+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds004 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses004 i) (axisDiagIds004 i) (hb i)
    (axis_diag_fields_4 i).1 (axis_diag_fields_4 i).2 (axis_fields_4 i)
end ThomsonNine.PackedMain
