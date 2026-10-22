import MainCoverage.AxisFields063
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_63 : ∀ i : Fin 32, AxisActualLower (axisLookup (2016+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds063 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses063 i) (axisDiagIds063 i) (hb i)
    (axis_diag_fields_63 i).1 (axis_diag_fields_63 i).2 (axis_fields_63 i)
end ThomsonNine.PackedMain
