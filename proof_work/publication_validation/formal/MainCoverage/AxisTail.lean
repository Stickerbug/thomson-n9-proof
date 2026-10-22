import MainCoverage.AxisData
set_option maxRecDepth 100000
namespace ThomsonNine.PackedMain
theorem axisLookup_tail (id : ℕ) (hi : 4809 ≤ id) : axisLookup id=axisLookup 4809 := by
  conv_lhs =>
    unfold axisLookup
    rw [ite_eq_right (by omega : ¬id<2432), ite_eq_right (by omega : ¬id<3648), ite_eq_right (by omega : ¬id<4224), ite_eq_right (by omega : ¬id<4544), ite_eq_right (by omega : ¬id<4672), ite_eq_right (by omega : ¬id<4736), ite_eq_right (by omega : ¬id<4800)]
    unfold axisBlock075
    rw [ite_eq_right (by omega : ¬id<4805), ite_eq_right (by omega : ¬id<4807), ite_eq_right (by omega : ¬id<4808), ite_eq_right (by omega : ¬id<4809)]
  rfl
end ThomsonNine.PackedMain
