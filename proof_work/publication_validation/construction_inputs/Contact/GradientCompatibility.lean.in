import ThomsonNine.Construction.Contact.LeftGradient
import ThomsonNine.Construction.Hermite.FamilyCurve

-- Isolated source: Contact.GradientCompatibility
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
noncomputable section
namespace ThomsonNine.ActualContact
open ThomsonNine.ActualHermite ThomsonNine.RationalListPolynomial Polynomial
open scoped BigOperators

theorem leftGradient_rhs : (∑ row : Fin 45, leftGradientWeight row*rhs row)=
    7*(∑ j : Fin 6, (energyWeights j : ℝ)*(value (energyNodes j))^3*pairVelocity j) := by
  have hr : RefinedRadius.radius^2<1 := by
    have hp : 0<(1-RefinedRadius.radius)*(1+RefinedRadius.radius) :=
      mul_pos (sub_pos.mpr RefinedRadius.radius_lt_one) (by linarith [RefinedRadius.radius_pos])
    nlinarith
  have hd1 : -1+RefinedRadius.radius^2≠0 := by nlinarith
  have hd2 : 2*RefinedRadius.radius^2-2≠0 := by nlinarith
  have hd4 : RefinedRadius.radius^2-4≠0 := by nlinarith
  norm_num [Fin.sum_univ_succ,leftGradientWeight,rhs,rows,point,gramGradient,Fin.add_def,
    energyWeights,energyNodes,pairVelocity,pairIndex,CandidateMoment.nodes,realPolynomial,ListPolynomial.polynomial,node]
  field_simp [hd1,hd2,hd4]
  ring_nf
  field_simp [hd1,hd2,hd4]
  ring

theorem leftGradient_rhs_zero : (∑ row : Fin 45, leftGradientWeight row*rhs row)=0 := by
  rw [leftGradient_rhs,pair_energy_stationary,mul_zero]
end ThomsonNine.ActualContact
