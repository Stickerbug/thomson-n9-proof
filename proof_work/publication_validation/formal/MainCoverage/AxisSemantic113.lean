import MainCoverage.AxisFields113
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_113 : ∀ i : Fin 32, AxisActualLower (axisLookup (3616+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds113 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses113 i) (axisDiagIds113 i) (hb i)
    (axis_diag_fields_113 i).1 (axis_diag_fields_113 i).2 (axis_fields_113 i)
end ThomsonNine.PackedMain
