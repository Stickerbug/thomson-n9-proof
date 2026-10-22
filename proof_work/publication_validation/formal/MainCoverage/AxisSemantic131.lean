import MainCoverage.AxisFields131
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_131 : ∀ i : Fin 32, AxisActualLower (axisLookup (4192+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds131 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses131 i) (axisDiagIds131 i) (hb i)
    (axis_diag_fields_131 i).1 (axis_diag_fields_131 i).2 (axis_fields_131 i)
end ThomsonNine.PackedMain
