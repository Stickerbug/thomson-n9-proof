import MainCoverage.AxisFields125
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_125 : ∀ i : Fin 32, AxisActualLower (axisLookup (4000+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds125 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses125 i) (axisDiagIds125 i) (hb i)
    (axis_diag_fields_125 i).1 (axis_diag_fields_125 i).2 (axis_fields_125 i)
end ThomsonNine.PackedMain
