import MainCoverage.AxisFields076
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_76 : ∀ i : Fin 32, AxisActualLower (axisLookup (2432+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds076 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses076 i) (axisDiagIds076 i) (hb i)
    (axis_diag_fields_76 i).1 (axis_diag_fields_76 i).2 (axis_fields_76 i)
end ThomsonNine.PackedMain
