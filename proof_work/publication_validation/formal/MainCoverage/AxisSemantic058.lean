import MainCoverage.AxisFields058
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_58 : ∀ i : Fin 32, AxisActualLower (axisLookup (1856+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds058 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses058 i) (axisDiagIds058 i) (hb i)
    (axis_diag_fields_58 i).1 (axis_diag_fields_58 i).2 (axis_fields_58 i)
end ThomsonNine.PackedMain
