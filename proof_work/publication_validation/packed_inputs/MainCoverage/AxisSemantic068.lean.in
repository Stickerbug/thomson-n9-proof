import MainCoverage.AxisFields068
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_68 : ∀ i : Fin 32, AxisActualLower (axisLookup (2176+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds068 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses068 i) (axisDiagIds068 i) (hb i)
    (axis_diag_fields_68 i).1 (axis_diag_fields_68 i).2 (axis_fields_68 i)
end ThomsonNine.PackedMain
