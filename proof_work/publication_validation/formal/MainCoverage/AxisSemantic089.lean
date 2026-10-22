import MainCoverage.AxisFields089
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_89 : ∀ i : Fin 32, AxisActualLower (axisLookup (2848+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds089 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses089 i) (axisDiagIds089 i) (hb i)
    (axis_diag_fields_89 i).1 (axis_diag_fields_89 i).2 (axis_fields_89 i)
end ThomsonNine.PackedMain
