import MainCoverage.AxisFields100
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_100 : ∀ i : Fin 32, AxisActualLower (axisLookup (3200+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds100 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses100 i) (axisDiagIds100 i) (hb i)
    (axis_diag_fields_100 i).1 (axis_diag_fields_100 i).2 (axis_fields_100 i)
end ThomsonNine.PackedMain
