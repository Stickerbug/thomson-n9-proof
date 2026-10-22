import MainCoverage.AxisFields001
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_1 : ∀ i : Fin 32, AxisActualLower (axisLookup (32+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds001 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses001 i) (axisDiagIds001 i) (hb i)
    (axis_diag_fields_1 i).1 (axis_diag_fields_1 i).2 (axis_fields_1 i)
end ThomsonNine.PackedMain
