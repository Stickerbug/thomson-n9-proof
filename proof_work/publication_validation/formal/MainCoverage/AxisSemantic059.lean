import MainCoverage.AxisFields059
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_59 : ∀ i : Fin 32, AxisActualLower (axisLookup (1888+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds059 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses059 i) (axisDiagIds059 i) (hb i)
    (axis_diag_fields_59 i).1 (axis_diag_fields_59 i).2 (axis_fields_59 i)
end ThomsonNine.PackedMain
