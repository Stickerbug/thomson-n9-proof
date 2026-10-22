import MainCoverage.AxisFields142
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_142 : ∀ i : Fin 32, AxisActualLower (axisLookup (4544+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds142 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses142 i) (axisDiagIds142 i) (hb i)
    (axis_diag_fields_142 i).1 (axis_diag_fields_142 i).2 (axis_fields_142 i)
end ThomsonNine.PackedMain
