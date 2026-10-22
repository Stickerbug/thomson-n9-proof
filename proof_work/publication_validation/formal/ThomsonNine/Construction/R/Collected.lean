import ThomsonNine.Construction.R.ExponentBridge
import ThomsonNine.Construction.R.GroupSemantics
import ThomsonNine.Construction.R.Partition

-- Isolated source: R.Collected
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
noncomputable section
namespace ThomsonNine.ActualR
open scoped BigOperators

def polynomial (u v t : ℝ) : ℝ :=
  ∑ j : Fin 807, coefficient j*QPolynomial.monomial (Data.sourceExponent j) u v t
def rawEval (u v t : ℝ) : ℝ :=
  ((List.range 3109).map (fun n => Collection.actualSourceCoefficient n*
    QPolynomial.monomial (Collection.sourceExponent n) u v t)).sum

theorem polynomial_eq_raw (u v t : ℝ) : polynomial u v t=rawEval u v t := by
  have h := FiniteCollector.collected_eval (List.finRange 807) Collection.groups 3109
    Collection.actualSourceCoefficient
    (fun n => QPolynomial.monomial (Collection.sourceExponent n) u v t)
    (fun j => QPolynomial.monomial (Data.sourceExponent j) u v t)
    Collection.partition (fun j _ n hn => by rw [Collection.group_exponent j n hn])
  simp only [Collection.group_actual] at h
  rw [MonomialSymmetry.finRange_sum] at h
  exact h
end ThomsonNine.ActualR
