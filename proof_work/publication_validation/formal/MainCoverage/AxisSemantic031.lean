import MainCoverage.AxisFields031
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_31 : ∀ i : Fin 32, AxisActualLower (axisLookup (992+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds031 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses031 i) (axisDiagIds031 i) (hb i)
    (axis_diag_fields_31 i).1 (axis_diag_fields_31 i).2 (axis_fields_31 i)
end ThomsonNine.PackedMain
