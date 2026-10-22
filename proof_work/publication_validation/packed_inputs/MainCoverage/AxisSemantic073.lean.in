import MainCoverage.AxisFields073
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_73 : ∀ i : Fin 32, AxisActualLower (axisLookup (2336+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds073 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses073 i) (axisDiagIds073 i) (hb i)
    (axis_diag_fields_73 i).1 (axis_diag_fields_73 i).2 (axis_fields_73 i)
end ThomsonNine.PackedMain
