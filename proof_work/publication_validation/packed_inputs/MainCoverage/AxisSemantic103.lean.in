import MainCoverage.AxisFields103
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_103 : ∀ i : Fin 32, AxisActualLower (axisLookup (3296+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds103 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses103 i) (axisDiagIds103 i) (hb i)
    (axis_diag_fields_103 i).1 (axis_diag_fields_103 i).2 (axis_fields_103 i)
end ThomsonNine.PackedMain
