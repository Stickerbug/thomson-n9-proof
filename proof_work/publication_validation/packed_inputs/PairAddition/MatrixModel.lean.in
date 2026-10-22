import PairAddition.Metadata
import Algebra.FiniteIntegerPolynomial

noncomputable section
namespace ThomsonNine.PairAddition
open scoped BigOperators
open ThomsonNine.IntegerListPolynomial

theorem matrixEntry_cons (c : Contribution) (cs : List Contribution) (i j : Fin 38) :
    matrixEntry (c::cs) i j=c.weight*(c.coefficients[i.val]?).getD 0*(c.coefficients[j.val]?).getD 0+
      matrixEntry cs i j := rfl

theorem matrix_eval (cs : List Contribution)
    (hl : ∀ c∈cs, c.coefficients.length≤38) (u v : ℝ) :
    (cs.map (fun c => (c.weight : ℝ)*(realPolynomial c.coefficients).eval u*
      (realPolynomial c.coefficients).eval v)).sum=
      ∑ i : Fin 38, ∑ j : Fin 38, (matrixEntry cs i j : ℝ)*u^i.val*v^j.val := by
  induction cs with
  | nil => simp [matrixEntry]
  | cons c cs ih =>
    have hc := hl c (by simp)
    have ht := ih (fun d hd => hl d (by simp [hd]))
    have hhead : (c.weight : ℝ)*(realPolynomial c.coefficients).eval u*(realPolynomial c.coefficients).eval v=
        ∑ i : Fin 38, ∑ j : Fin 38,
          ((c.weight*(c.coefficients[i.val]?).getD 0*(c.coefficients[j.val]?).getD 0 : ℤ) : ℝ)*u^i.val*v^j.val := by
      rw [eval_fin_sum 38 c.coefficients hc u,eval_fin_sum 38 c.coefficients hc v]
      simp only [Finset.mul_sum,Finset.sum_mul,Int.cast_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    change (c.weight : ℝ)*(realPolynomial c.coefficients).eval u*(realPolynomial c.coefficients).eval v+
      (cs.map (fun c => (c.weight : ℝ)*(realPolynomial c.coefficients).eval u*(realPolynomial c.coefficients).eval v)).sum=_
    rw [hhead,ht]
    simp only [matrixEntry_cons,Int.cast_add,add_mul,Finset.sum_add_distrib]

theorem diagonal_matrix_eval (cs : List Contribution) (diagonal : Fin 38 → ℤ)
    (hl : ∀ c∈cs, c.coefficients.length≤38)
    (hM : ∀ i j : Fin 38, matrixEntry cs i j=if i=j then diagonal i else 0) (u v : ℝ) :
    (cs.map (fun c => (c.weight : ℝ)*(realPolynomial c.coefficients).eval u*
      (realPolynomial c.coefficients).eval v)).sum=
      ∑ i : Fin 38, (diagonal i : ℝ)*(u*v)^i.val := by
  rw [matrix_eval cs hl u v]
  simp [hM,mul_pow,mul_assoc]
end ThomsonNine.PairAddition
