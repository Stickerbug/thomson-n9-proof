import MainCoverage.AxisFields098
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_98 : ∀ i : Fin 32, AxisActualLower (axisLookup (3136+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds098 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses098 i) (axisDiagIds098 i) (hb i)
    (axis_diag_fields_98 i).1 (axis_diag_fields_98 i).2 (axis_fields_98 i)
end ThomsonNine.PackedMain
