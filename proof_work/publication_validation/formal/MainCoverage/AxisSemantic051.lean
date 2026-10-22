import MainCoverage.AxisFields051
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_51 : ∀ i : Fin 32, AxisActualLower (axisLookup (1632+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds051 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses051 i) (axisDiagIds051 i) (hb i)
    (axis_diag_fields_51 i).1 (axis_diag_fields_51 i).2 (axis_fields_51 i)
end ThomsonNine.PackedMain
