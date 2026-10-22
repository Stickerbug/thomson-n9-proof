import Algebra.RationalPolynomialCoefficient

noncomputable section
namespace ThomsonNine.RationalListPolynomial
open Polynomial
open scoped BigOperators
theorem eval_fin_sum (n : ℕ) (l : List ℚ) (hl : l.length≤n) (x : ℝ) :
    (realPolynomial l).eval x=∑ i : Fin n, (((l[i.val]?).getD 0 : ℚ) : ℝ)*x^i.val := by
  induction n generalizing l with
  | zero =>
    have he : l=[] := List.length_eq_zero_iff.mp (by omega)
    simp [he,realPolynomial,ListPolynomial.polynomial]
  | succ n ih =>
    cases l with
    | nil => simp [realPolynomial,ListPolynomial.polynomial]
    | cons a l =>
      rw [cons,eval_add,eval_C,eval_mul,eval_X,ih l (by simpa using hl)]
      simp only [Fin.sum_univ_succ,Fin.val_zero,List.getElem?_cons_zero,Option.getD_some,pow_zero,mul_one,
        Fin.val_succ,List.getElem?_cons_succ]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [pow_succ]
      ring
end ThomsonNine.RationalListPolynomial
