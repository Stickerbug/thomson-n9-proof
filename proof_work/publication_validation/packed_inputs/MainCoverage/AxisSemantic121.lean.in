import MainCoverage.AxisFields121
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_121 : ∀ i : Fin 32, AxisActualLower (axisLookup (3872+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds121 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses121 i) (axisDiagIds121 i) (hb i)
    (axis_diag_fields_121 i).1 (axis_diag_fields_121 i).2 (axis_fields_121 i)
end ThomsonNine.PackedMain
