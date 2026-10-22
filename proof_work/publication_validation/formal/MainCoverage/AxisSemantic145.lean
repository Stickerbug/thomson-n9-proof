import MainCoverage.AxisFields145
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_145 : ∀ i : Fin 32, AxisActualLower (axisLookup (4640+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds145 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses145 i) (axisDiagIds145 i) (hb i)
    (axis_diag_fields_145 i).1 (axis_diag_fields_145 i).2 (axis_fields_145 i)
end ThomsonNine.PackedMain
