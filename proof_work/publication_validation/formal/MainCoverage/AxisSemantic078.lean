import MainCoverage.AxisFields078
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_78 : ∀ i : Fin 32, AxisActualLower (axisLookup (2496+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds078 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses078 i) (axisDiagIds078 i) (hb i)
    (axis_diag_fields_78 i).1 (axis_diag_fields_78 i).2 (axis_fields_78 i)
end ThomsonNine.PackedMain
