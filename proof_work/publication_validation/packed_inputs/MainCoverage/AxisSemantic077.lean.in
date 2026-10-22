import MainCoverage.AxisFields077
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_77 : ∀ i : Fin 32, AxisActualLower (axisLookup (2464+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds077 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses077 i) (axisDiagIds077 i) (hb i)
    (axis_diag_fields_77 i).1 (axis_diag_fields_77 i).2 (axis_fields_77 i)
end ThomsonNine.PackedMain
