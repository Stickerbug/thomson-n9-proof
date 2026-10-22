import LocalShift.BoundaryContact
import Algebra.GramCurve

noncomputable section
namespace ThomsonNine.LocalShift

theorem center_interval_mem (localId : Fin 12) (axis : Fin 3) :
    (centerInterval localId axis).mem (center localId axis) :=
  FixedInterval.mem_to_rat (ActualHermite.CoefficientData.inputNode_mem (labels localId axis))
    ActualHermite.CoefficientData.unitScale_pos (node_to_center_bounds localId axis).1 (node_to_center_bounds localId axis).2

theorem lowerGraph_self (a : ℝ) (ha : a^2≤1) : LocalLDL.lowerGraph a a=2*a^2-1 := by
  have hp : 0≤1-a^2 := by linarith
  unfold LocalLDL.lowerGraph
  rw [show (1-a^2)*(1-a^2)=(1-a^2)^2 by ring,Real.sqrt_sq_eq_abs,abs_of_nonneg hp]
  ring

theorem lowerGraph_GB (r : ℝ) (hr : 0<r) (hr1 : r<1) :
    LocalLDL.lowerGraph (-r) (2*r^2-1)=-r := by
  have hr2 : r^2<1 := by nlinarith
  have hp : 0≤2*r*(1-r^2) := le_of_lt (mul_pos (mul_pos (by norm_num) hr) (by linarith))
  have he : (1-(-r)^2)*(1-(2*r^2-1)^2)=(2*r*(1-r^2))^2 := by ring
  unfold LocalLDL.lowerGraph
  rw [he,Real.sqrt_sq_eq_abs,abs_of_nonneg hp]
  ring

theorem center_graph (localId : Fin 12) (hb : IsBoundary localId) :
    GramGraph.point (center localId 1) (center localId 2)=center localId := by
  have hr := RefinedRadius.radius_pos
  have hr1 := RefinedRadius.radius_lt_one
  have hr2 : RefinedRadius.radius^2<1 := by nlinarith
  rcases hb with h | h | h <;> subst localId
  · funext a
    fin_cases a
    · exact lowerGraph_GB RefinedRadius.radius hr hr1
    · rfl
    · rfl
  · funext a
    fin_cases a
    · change LocalLDL.lowerGraph (RefinedRadius.radius/2) (RefinedRadius.radius/2)=RefinedRadius.radius^2/2-1
      rw [lowerGraph_self _ (by nlinarith)]
      ring
    · rfl
    · rfl
  · funext a
    fin_cases a
    · change LocalLDL.lowerGraph (-1/2 : ℝ) (-1/2)=(-1/2 : ℝ)
      rw [lowerGraph_self _ (by norm_num)]
      norm_num
    · rfl
    · rfl
end ThomsonNine.LocalShift
