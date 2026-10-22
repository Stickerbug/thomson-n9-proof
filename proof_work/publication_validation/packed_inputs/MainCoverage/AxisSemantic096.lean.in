import MainCoverage.AxisFields096
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_96 : ∀ i : Fin 32, AxisActualLower (axisLookup (3072+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds096 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses096 i) (axisDiagIds096 i) (hb i)
    (axis_diag_fields_96 i).1 (axis_diag_fields_96 i).2 (axis_fields_96 i)
end ThomsonNine.PackedMain
