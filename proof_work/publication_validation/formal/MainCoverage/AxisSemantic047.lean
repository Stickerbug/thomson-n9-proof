import MainCoverage.AxisFields047
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_47 : ∀ i : Fin 32, AxisActualLower (axisLookup (1504+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds047 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses047 i) (axisDiagIds047 i) (hb i)
    (axis_diag_fields_47 i).1 (axis_diag_fields_47 i).2 (axis_fields_47 i)
end ThomsonNine.PackedMain
