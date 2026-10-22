import MainCoverage.AxisFields024
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_24 : ∀ i : Fin 32, AxisActualLower (axisLookup (768+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds024 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses024 i) (axisDiagIds024 i) (hb i)
    (axis_diag_fields_24 i).1 (axis_diag_fields_24 i).2 (axis_fields_24 i)
end ThomsonNine.PackedMain
