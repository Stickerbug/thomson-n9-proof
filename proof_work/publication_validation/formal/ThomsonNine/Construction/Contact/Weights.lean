import ThomsonNine.Construction.Contact.ValueBinding
import ThomsonNine.Construction.Moment.Function

-- Isolated source: Contact.Weights
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
noncomputable section
namespace ThomsonNine.ActualContact
open ThomsonNine.ContactJet
open scoped BigOperators

def valueRows : Fin 12 → Fin 45 := ![0,4,8,12,16,20,24,27,30,34,37,41]
def triangleWeights : Fin 12 → ℚ := ![2,12,6,6,12,6,3,6,12,1,6,12]
def contactPoint (pt : Fin 19) : Point :=
  if h : pt.val<12 then point (valueRows ⟨pt.val,h⟩)
  else if h' : pt.val<18 then diagonal (energyNodes ⟨pt.val-12,by omega⟩)
  else ones

theorem actual_moment_points (pt : Fin 19) (j : Fin 3) :
    CandidateMoment.realPoint RefinedRadius.radius pt j=contactPoint pt j := by
  fin_cases pt <;> fin_cases j <;>
    norm_num [CandidateMoment.realPoint,CandidateMoment.realNodes,CandidateMoment.nodes,
      CandidateMoment.points,contactPoint,point,diagonal,ones,energyNodes,rows,valueRows,
      RationalListPolynomial.realPolynomial,ListPolynomial.polynomial,ActualHermite.node] <;> ring

theorem weighted_polynomialContact (X : Fin 190 → ℝ) :
    (∑ j : Fin 12, (triangleWeights j : ℝ)*polynomialContact X (point (valueRows j)))=
      7*CandidateMoment.weightedF X RefinedRadius.radius := by
  simp only [CandidateMoment.weightedF,actual_moment_points]
  norm_num [Fin.sum_univ_succ,polynomialContact,contactPoint,CandidateMoment.weight,
    point,diagonal,ones,energyNodes,rows,valueRows,triangleWeights]
  ring

theorem value_M (j : Fin 12) (h : Fin 190) : M (valueRows j) h=valueRow (valueRows j) h := by
  fin_cases j <;> rfl

theorem weighted_rhs : (∑ j : Fin 12, (triangleWeights j : ℝ)*rhs (valueRows j))=0 := by
  norm_num [Fin.sum_univ_succ,rhs,rows,valueRows,triangleWeights,E,energyNodes,energyWeights]
  ring

theorem weighted_value_M (X : Fin 190 → ℝ) :
    (∑ j : Fin 12, (triangleWeights j : ℝ)*(∑ h : Fin 190, M (valueRows j) h*X h))=
      7*CandidateMoment.weightedF X RefinedRadius.radius := by
  have hj (j : Fin 12) : (∑ h : Fin 190, M (valueRows j) h*X h)=polynomialContact X (point (valueRows j)) := by
    simp only [value_M,mul_comm]
    exact valueRow_sum X (valueRows j)
  simp only [hj,weighted_polynomialContact]
end ThomsonNine.ActualContact
