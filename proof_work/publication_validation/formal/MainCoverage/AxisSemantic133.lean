import MainCoverage.AxisFields133
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_133 : ∀ i : Fin 32, AxisActualLower (axisLookup (4256+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds133 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses133 i) (axisDiagIds133 i) (hb i)
    (axis_diag_fields_133 i).1 (axis_diag_fields_133 i).2 (axis_fields_133 i)
end ThomsonNine.PackedMain
