import MainCoverage.AxisFields060
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_60 : ∀ i : Fin 32, AxisActualLower (axisLookup (1920+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds060 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses060 i) (axisDiagIds060 i) (hb i)
    (axis_diag_fields_60 i).1 (axis_diag_fields_60 i).2 (axis_fields_60 i)
end ThomsonNine.PackedMain
