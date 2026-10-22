import MainCoverage.AxisFields075
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_75 : ∀ i : Fin 32, AxisActualLower (axisLookup (2400+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds075 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses075 i) (axisDiagIds075 i) (hb i)
    (axis_diag_fields_75 i).1 (axis_diag_fields_75 i).2 (axis_fields_75 i)
end ThomsonNine.PackedMain
