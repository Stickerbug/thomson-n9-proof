import MainCoverage.AxisFields126
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_126 : ∀ i : Fin 32, AxisActualLower (axisLookup (4032+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds126 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses126 i) (axisDiagIds126 i) (hb i)
    (axis_diag_fields_126 i).1 (axis_diag_fields_126 i).2 (axis_fields_126 i)
end ThomsonNine.PackedMain
