import MainCoverage.AxisFields030
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_30 : ∀ i : Fin 32, AxisActualLower (axisLookup (960+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds030 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses030 i) (axisDiagIds030 i) (hb i)
    (axis_diag_fields_30 i).1 (axis_diag_fields_30 i).2 (axis_fields_30 i)
end ThomsonNine.PackedMain
