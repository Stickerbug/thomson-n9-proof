import MainCoverage.AxisFields129
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_129 : ∀ i : Fin 32, AxisActualLower (axisLookup (4128+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds129 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses129 i) (axisDiagIds129 i) (hb i)
    (axis_diag_fields_129 i).1 (axis_diag_fields_129 i).2 (axis_fields_129 i)
end ThomsonNine.PackedMain
