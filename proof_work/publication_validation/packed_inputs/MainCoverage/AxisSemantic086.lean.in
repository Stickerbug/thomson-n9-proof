import MainCoverage.AxisFields086
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_86 : ∀ i : Fin 32, AxisActualLower (axisLookup (2752+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds086 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses086 i) (axisDiagIds086 i) (hb i)
    (axis_diag_fields_86 i).1 (axis_diag_fields_86 i).2 (axis_fields_86 i)
end ThomsonNine.PackedMain
