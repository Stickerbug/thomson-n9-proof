import MainCoverage.AxisFields107
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_107 : ∀ i : Fin 32, AxisActualLower (axisLookup (3424+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds107 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses107 i) (axisDiagIds107 i) (hb i)
    (axis_diag_fields_107 i).1 (axis_diag_fields_107 i).2 (axis_fields_107 i)
end ThomsonNine.PackedMain
