import MainCoverage.AxisFields056
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_56 : ∀ i : Fin 32, AxisActualLower (axisLookup (1792+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds056 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses056 i) (axisDiagIds056 i) (hb i)
    (axis_diag_fields_56 i).1 (axis_diag_fields_56 i).2 (axis_fields_56 i)
end ThomsonNine.PackedMain
