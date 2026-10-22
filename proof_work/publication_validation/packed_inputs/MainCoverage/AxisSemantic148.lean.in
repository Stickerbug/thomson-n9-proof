import MainCoverage.AxisFields148
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_148 : ∀ i : Fin 32, AxisActualLower (axisLookup (4736+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds148 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses148 i) (axisDiagIds148 i) (hb i)
    (axis_diag_fields_148 i).1 (axis_diag_fields_148 i).2 (axis_fields_148 i)
end ThomsonNine.PackedMain
