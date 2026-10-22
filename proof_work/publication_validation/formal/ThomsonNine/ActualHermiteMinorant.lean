import ThomsonNine.ActualQuotientBernstein
import ThomsonNine.HermiteMinorant

noncomputable section
namespace ThomsonNine.ActualHermite.QuotientBernstein
open Polynomial ThomsonNine.RationalListPolynomial
open ThomsonNine.ActualHermite.QuotientStructure
open scoped BigOperators

theorem Q_bernstein_representation : Q = ∑ i : Fin 28, C (beta i)*B i := by
  calc
    Q = ∑ j : Fin 28, C (Q.coeff j)*X^(j : ℕ) := by
      rw [Fin.sum_univ_eq_sum_range (fun j => C (Q.coeff j)*X^j)]
      exact Q.as_sum_range_C_mul_X_pow' (Q_natDegree.trans_lt (by omega))
    _ = ∑ j : Fin 28, C (Q.coeff j)*(∑ i : Fin 28, C (matrix i j : ℝ)*B i) := by
      exact Finset.sum_congr rfl (fun j _ => by rw [monomial_identity])
    _ = ∑ i : Fin 28, C (beta i)*B i := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [beta,map_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_mul]
      ring

theorem Q_nonnegative (t : ℝ) (ht : -1≤t ∧ t≤1) : 0≤Q.eval t := by
  rw [Q_bernstein_representation,eval_finset_sum]
  apply Finset.sum_nonneg
  intro i hi
  rw [eval_mul,eval_C]
  exact mul_nonneg (le_of_lt (beta_positive i)) (B_nonnegative i t ht)

theorem H_minorant (t : ℝ) (ht : -1≤t ∧ t<1) :
    H.eval t ≤ (Real.sqrt (2-2*t))⁻¹ := by
  exact HermiteFactor.minorant_of_factor H Q node QuotientStructure.factor t
    ht.2 (Q_nonnegative t ⟨ht.1,le_of_lt ht.2⟩)
end ThomsonNine.ActualHermite.QuotientBernstein
