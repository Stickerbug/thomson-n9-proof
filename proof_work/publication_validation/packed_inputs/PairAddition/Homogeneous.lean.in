import PairAddition.Metadata
import ThomsonNine.ThreePoint

noncomputable section
namespace ThomsonNine.PairAddition
open scoped BigOperators
def homogeneous (m : Fin 38) (w d : ℝ) : ℝ :=
  ∑ h : Fin 38, (qCoefficient m h : ℝ)*w^h.val*d^((m.val-h.val)/2)
end ThomsonNine.PairAddition
