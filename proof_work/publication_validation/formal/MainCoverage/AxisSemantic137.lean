import MainCoverage.AxisFields137
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_137 : ∀ i : Fin 32, AxisActualLower (axisLookup (4384+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds137 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses137 i) (axisDiagIds137 i) (hb i)
    (axis_diag_fields_137 i).1 (axis_diag_fields_137 i).2 (axis_fields_137 i)
end ThomsonNine.PackedMain
