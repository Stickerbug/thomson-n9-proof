import MainCoverage.AxisFields067
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_67 : ∀ i : Fin 32, AxisActualLower (axisLookup (2144+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds067 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses067 i) (axisDiagIds067 i) (hb i)
    (axis_diag_fields_67 i).1 (axis_diag_fields_67 i).2 (axis_fields_67 i)
end ThomsonNine.PackedMain
