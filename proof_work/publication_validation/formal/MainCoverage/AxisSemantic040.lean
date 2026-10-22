import MainCoverage.AxisFields040
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_40 : ∀ i : Fin 32, AxisActualLower (axisLookup (1280+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds040 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses040 i) (axisDiagIds040 i) (hb i)
    (axis_diag_fields_40 i).1 (axis_diag_fields_40 i).2 (axis_fields_40 i)
end ThomsonNine.PackedMain
