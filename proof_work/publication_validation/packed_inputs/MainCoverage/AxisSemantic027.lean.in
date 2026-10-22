import MainCoverage.AxisFields027
import MainCoverage.AxisMeaning
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axis_actual_27 : ∀ i : Fin 32, AxisActualLower (axisLookup (864+i.val)) := by
  have hb : ∀ i : Fin 32, axisDiagIds027 i<4816 := by decide +kernel
  intro i
  exact axis_witness_actual _ (axisWitnesses027 i) (axisDiagIds027 i) (hb i)
    (axis_diag_fields_27 i).1 (axis_diag_fields_27 i).2 (axis_fields_27 i)
end ThomsonNine.PackedMain
