import MainCoverage.AxisFields052
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_52 : ∀ i : Fin 32, AxisActualLower (axisLookup (1664+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds052 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses052 i) (axisDiagIds052 i) (hb i)
    (axis_diag_fields_52 i).1 (axis_diag_fields_52 i).2 (axis_fields_52 i)
end ThomsonNine.PackedMain
