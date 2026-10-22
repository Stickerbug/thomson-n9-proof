import MainCoverage.AxisFields069
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_69 : ∀ i : Fin 32, AxisActualLower (axisLookup (2208+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds069 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses069 i) (axisDiagIds069 i) (hb i)
    (axis_diag_fields_69 i).1 (axis_diag_fields_69 i).2 (axis_fields_69 i)
end ThomsonNine.PackedMain
