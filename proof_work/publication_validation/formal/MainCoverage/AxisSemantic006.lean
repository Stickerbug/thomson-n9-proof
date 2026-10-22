import MainCoverage.AxisFields006
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_6 : ∀ i : Fin 32, AxisActualLower (axisLookup (192+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds006 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses006 i) (axisDiagIds006 i) (hb i)
    (axis_diag_fields_6 i).1 (axis_diag_fields_6 i).2 (axis_fields_6 i)
end ThomsonNine.PackedMain
