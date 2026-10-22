import MainCoverage.AxisFields108
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_108 : ∀ i : Fin 32, AxisActualLower (axisLookup (3456+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds108 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses108 i) (axisDiagIds108 i) (hb i)
    (axis_diag_fields_108 i).1 (axis_diag_fields_108 i).2 (axis_fields_108 i)
end ThomsonNine.PackedMain
