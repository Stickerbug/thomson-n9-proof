import MainCoverage.AxisFields043
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_43 : ∀ i : Fin 32, AxisActualLower (axisLookup (1376+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds043 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses043 i) (axisDiagIds043 i) (hb i)
    (axis_diag_fields_43 i).1 (axis_diag_fields_43 i).2 (axis_fields_43 i)
end ThomsonNine.PackedMain
