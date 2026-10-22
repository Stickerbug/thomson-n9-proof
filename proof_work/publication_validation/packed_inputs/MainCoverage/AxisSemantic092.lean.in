import MainCoverage.AxisFields092
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_92 : ∀ i : Fin 32, AxisActualLower (axisLookup (2944+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds092 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses092 i) (axisDiagIds092 i) (hb i)
    (axis_diag_fields_92 i).1 (axis_diag_fields_92 i).2 (axis_fields_92 i)
end ThomsonNine.PackedMain
