import MainCoverage.AxisFields062
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_62 : ∀ i : Fin 32, AxisActualLower (axisLookup (1984+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds062 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses062 i) (axisDiagIds062 i) (hb i)
    (axis_diag_fields_62 i).1 (axis_diag_fields_62 i).2 (axis_fields_62 i)
end ThomsonNine.PackedMain
