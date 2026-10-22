import Contact.RowBinding
import Contact.RowClasses
import Contact.GradientMoment
set_option pp.maxSteps 2000000
set_option pp.deepTerms true
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
noncomputable section
namespace ThomsonNine.ActualContact
open ThomsonNine.ContactJet ThomsonNine.RationalListPolynomial Polynomial
open scoped BigOperators
attribute [local irreducible] FJet contactGradient classGradient

def leftGradientWeight : Fin 45 → ℝ := ![(0),
(-6*RefinedRadius.radius),
(-6*RefinedRadius.radius),
(-6*RefinedRadius.radius),
(0),
(-36*RefinedRadius.radius),
(48*RefinedRadius.radius),
(12*RefinedRadius.radius),
(0),
(-18*RefinedRadius.radius),
(6*RefinedRadius.radius),
(6*RefinedRadius.radius),
(0),
(-18*RefinedRadius.radius),
(3),
(3),
(0),
(-36*RefinedRadius.radius),
(6),
(-12),
(0),
(24*RefinedRadius.radius),
(3),
(3),
(0),
(3/(2*RefinedRadius.radius^2 - 2)),
(3/(2*RefinedRadius.radius^2 - 2)),
(0),
(-6/(RefinedRadius.radius^2 - 4)),
(-6/(RefinedRadius.radius^2 - 4)),
(0),
(12*RefinedRadius.radius),
(6),
(-12),
(0),
(0),
(0),
(0),
(0),
(3),
(3),
(0),
(0),
(6),
(-12)]

theorem leftGradient_identity (X : Fin 190 → ℝ) :
    weightedGradient X=(∑ row : Fin 45, leftGradientWeight row*(∑ h : Fin 190, M row h*X h)) := by
  have hr : RefinedRadius.radius^2<1 := by
    have hp : 0<(1-RefinedRadius.radius)*(1+RefinedRadius.radius) :=
      mul_pos (sub_pos.mpr RefinedRadius.radius_lt_one) (by linarith [RefinedRadius.radius_pos])
    nlinarith
  have hd1 : -1+RefinedRadius.radius^2≠0 := by nlinarith
  have hd2 : 2*RefinedRadius.radius^2-2≠0 := by nlinarith
  have hd4 : RefinedRadius.radius^2-4≠0 := by nlinarith
  simp only [row_sum,weightedGradient,gradient_eq_class]
  norm_num [rowClass,Fin.sum_univ_succ,leftGradientWeight,triangleWeights,curveVelocity,point,rows,valueRows,
    gramGradient,Fin.add_def,CandidateMoment.nodes,CandidateMoment.points,realPolynomial,ListPolynomial.polynomial,ActualHermite.node]
  field_simp [hd1,hd2,hd4]
  ring_nf
  field_simp [hd1,hd2,hd4]
  ring

theorem leftGradient_matrix_zero (X : Fin 190 → ℝ) :
    (∑ row : Fin 45, leftGradientWeight row*(∑ h : Fin 190, M row h*X h))=0 := by
  rw [← leftGradient_identity]
  exact actual_weightedGradient_zero X
end ThomsonNine.ActualContact
