import MainCoverage.AxisFields050
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_50 : ∀ i : Fin 32, AxisActualLower (axisLookup (1600+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds050 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses050 i) (axisDiagIds050 i) (hb i)
    (axis_diag_fields_50 i).1 (axis_diag_fields_50 i).2 (axis_fields_50 i)
end ThomsonNine.PackedMain
