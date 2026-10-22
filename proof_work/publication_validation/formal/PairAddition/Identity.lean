import PairAddition.ContributionModel

noncomputable section
namespace ThomsonNine.PairAddition
open Polynomial
open scoped BigOperators

theorem addition_identity (u v t : ℝ) : P.eval t=
    ∑ f : Fin 138, ((features f).weight : ℝ)*phi f u*phi f v*
      ThreePoint.Q3 (features f).order.val u v t := by
  have he := P_shifted_eval (u*v) (t-u*v)
  rw [sub_add_cancel] at he
  rw [he]
  simp_rw [← coefficient_identity]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f hf
  rw [← homogeneous_eq_Q3 (features f).order.val (features f).order.isLt u v t]
  simp only [homogeneous,Finset.mul_sum,termCoefficient]
  apply Finset.sum_congr rfl
  intro h hh
  ring
end ThomsonNine.PairAddition
