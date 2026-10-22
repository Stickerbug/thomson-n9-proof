import MainCoverage.AxisFields080
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_80 : ∀ i : Fin 32, AxisActualLower (axisLookup (2560+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds080 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses080 i) (axisDiagIds080 i) (hb i)
    (axis_diag_fields_80 i).1 (axis_diag_fields_80 i).2 (axis_fields_80 i)
end ThomsonNine.PackedMain
