import MainCoverage.AxisFields071
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_71 : ∀ i : Fin 32, AxisActualLower (axisLookup (2272+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds071 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses071 i) (axisDiagIds071 i) (hb i)
    (axis_diag_fields_71 i).1 (axis_diag_fields_71 i).2 (axis_fields_71 i)
end ThomsonNine.PackedMain
