import MainCoverage.AxisFields055
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_55 : ∀ i : Fin 32, AxisActualLower (axisLookup (1760+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds055 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses055 i) (axisDiagIds055 i) (hb i)
    (axis_diag_fields_55 i).1 (axis_diag_fields_55 i).2 (axis_fields_55 i)
end ThomsonNine.PackedMain
