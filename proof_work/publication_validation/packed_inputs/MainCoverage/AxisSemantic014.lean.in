import MainCoverage.AxisFields014
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_14 : ∀ i : Fin 32, AxisActualLower (axisLookup (448+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds014 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses014 i) (axisDiagIds014 i) (hb i)
    (axis_diag_fields_14 i).1 (axis_diag_fields_14 i).2 (axis_fields_14 i)
end ThomsonNine.PackedMain
