import MainCoverage.AxisFields119
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_119 : ∀ i : Fin 32, AxisActualLower (axisLookup (3808+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds119 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses119 i) (axisDiagIds119 i) (hb i)
    (axis_diag_fields_119 i).1 (axis_diag_fields_119 i).2 (axis_fields_119 i)
end ThomsonNine.PackedMain
