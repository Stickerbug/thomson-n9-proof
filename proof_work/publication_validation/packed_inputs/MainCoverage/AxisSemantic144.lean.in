import MainCoverage.AxisFields144
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_144 : ∀ i : Fin 32, AxisActualLower (axisLookup (4608+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds144 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses144 i) (axisDiagIds144 i) (hb i)
    (axis_diag_fields_144 i).1 (axis_diag_fields_144 i).2 (axis_fields_144 i)
end ThomsonNine.PackedMain
