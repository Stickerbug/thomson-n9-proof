import MainCoverage.AxisFields115
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_115 : ∀ i : Fin 32, AxisActualLower (axisLookup (3680+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds115 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses115 i) (axisDiagIds115 i) (hb i)
    (axis_diag_fields_115 i).1 (axis_diag_fields_115 i).2 (axis_fields_115 i)
end ThomsonNine.PackedMain
