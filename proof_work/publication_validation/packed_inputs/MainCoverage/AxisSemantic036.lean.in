import MainCoverage.AxisFields036
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_36 : ∀ i : Fin 32, AxisActualLower (axisLookup (1152+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds036 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses036 i) (axisDiagIds036 i) (hb i)
    (axis_diag_fields_36 i).1 (axis_diag_fields_36 i).2 (axis_fields_36 i)
end ThomsonNine.PackedMain
