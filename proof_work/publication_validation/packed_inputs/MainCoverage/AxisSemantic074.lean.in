import MainCoverage.AxisFields074
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_74 : ∀ i : Fin 32, AxisActualLower (axisLookup (2368+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds074 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses074 i) (axisDiagIds074 i) (hb i)
    (axis_diag_fields_74 i).1 (axis_diag_fields_74 i).2 (axis_fields_74 i)
end ThomsonNine.PackedMain
