import MainCoverage.AxisFields135
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_135 : ∀ i : Fin 32, AxisActualLower (axisLookup (4320+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds135 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses135 i) (axisDiagIds135 i) (hb i)
    (axis_diag_fields_135 i).1 (axis_diag_fields_135 i).2 (axis_fields_135 i)
end ThomsonNine.PackedMain
