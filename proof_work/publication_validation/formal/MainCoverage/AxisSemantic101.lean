import MainCoverage.AxisFields101
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_101 : ∀ i : Fin 32, AxisActualLower (axisLookup (3232+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds101 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses101 i) (axisDiagIds101 i) (hb i)
    (axis_diag_fields_101 i).1 (axis_diag_fields_101 i).2 (axis_fields_101 i)
end ThomsonNine.PackedMain
