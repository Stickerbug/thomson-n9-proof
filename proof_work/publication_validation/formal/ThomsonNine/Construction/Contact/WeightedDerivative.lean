import ThomsonNine.Construction.Contact.Weights
import ThomsonNine.Construction.Contact.CurveDerivative

-- Isolated source: Contact.WeightedDerivative
set_option maxRecDepth 100000
noncomputable section
namespace ThomsonNine.ActualContact
open ThomsonNine.ContactJet ThomsonNine.RationalListPolynomial Polynomial
open scoped BigOperators

def curvePoint (j : Fin 12) (r : ℝ) : Point := CandidateMoment.realPoint r ⟨j.val,by omega⟩
def curveVelocity (j : Fin 12) (a : Fin 3) : ℝ :=
  (realPolynomial (CandidateMoment.nodes (CandidateMoment.points ⟨j.val,by omega⟩ a))).derivative.eval RefinedRadius.radius

theorem curvePoint_at (j : Fin 12) : curvePoint j RefinedRadius.radius=point (valueRows j) := by
  funext a
  have h := actual_moment_points ⟨j.val,by omega⟩ a
  simpa [curvePoint,contactPoint,j.isLt] using h

theorem curvePoint_derivative (j : Fin 12) (a : Fin 3) :
    HasDerivAt (fun r => curvePoint j r a) (curveVelocity j a) RefinedRadius.radius :=
  (realPolynomial (CandidateMoment.nodes (CandidateMoment.points ⟨j.val,by omega⟩ a))).hasDerivAt RefinedRadius.radius

theorem weighted_polynomialContact_curve (X : Fin 190 → ℝ) (r : ℝ) :
    (∑ j : Fin 12, (triangleWeights j : ℝ)*polynomialContact X (curvePoint j r))=
      7*CandidateMoment.weightedF X r := by
  norm_num [Fin.sum_univ_succ,polynomialContact,curvePoint,CandidateMoment.weightedF,
    CandidateMoment.realPoint,CandidateMoment.realNodes,CandidateMoment.nodes,CandidateMoment.points,
    CandidateMoment.weight,triangleWeights,realPolynomial,ListPolynomial.polynomial]
  ring

def weightedGradient (X : Fin 190 → ℝ) : ℝ :=
  ∑ j : Fin 12, (triangleWeights j : ℝ)*
    (∑ a : Fin 3, contactGradient X (point (valueRows j)) a*curveVelocity j a)

theorem weightedGradient_zero_of_stationary (X : Fin 190 → ℝ)
    (hF : HasDerivAt (CandidateMoment.weightedF X) 0 RefinedRadius.radius) : weightedGradient X=0 := by
  have hd (j : Fin 12) :
      HasDerivAt (fun r => (triangleWeights j : ℝ)*polynomialContact X (curvePoint j r))
        ((triangleWeights j : ℝ)*(∑ a : Fin 3, contactGradient X (point (valueRows j)) a*curveVelocity j a))
        RefinedRadius.radius :=
    (polynomialContact_derivative X (point (valueRows j)) (curvePoint j) (curveVelocity j)
      RefinedRadius.radius (curvePoint_at j) (curvePoint_derivative j)).const_mul _
  have hsum := HasDerivAt.fun_sum (u:=Finset.univ) (fun j _ => hd j)
  have he : (fun r => ∑ j : Fin 12, (triangleWeights j : ℝ)*polynomialContact X (curvePoint j r))=
      (fun r => 7*CandidateMoment.weightedF X r) := by
    funext r
    exact weighted_polynomialContact_curve X r
  rw [he] at hsum
  have hzero := hF.const_mul 7
  have h := hsum.unique hzero
  change weightedGradient X=7*0 at h
  simpa only [mul_zero] using h
end ThomsonNine.ActualContact
