import MainCoverage.AxisFields093
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_93 : ∀ i : Fin 32, AxisActualLower (axisLookup (2976+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds093 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses093 i) (axisDiagIds093 i) (hb i)
    (axis_diag_fields_93 i).1 (axis_diag_fields_93 i).2 (axis_fields_93 i)
end ThomsonNine.PackedMain
