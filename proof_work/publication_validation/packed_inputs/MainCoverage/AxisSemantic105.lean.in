import MainCoverage.AxisFields105
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_105 : ∀ i : Fin 32, AxisActualLower (axisLookup (3360+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds105 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses105 i) (axisDiagIds105 i) (hb i)
    (axis_diag_fields_105 i).1 (axis_diag_fields_105 i).2 (axis_fields_105 i)
end ThomsonNine.PackedMain
