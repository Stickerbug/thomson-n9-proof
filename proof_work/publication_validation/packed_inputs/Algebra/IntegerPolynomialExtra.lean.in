import Algebra.IntegerPolynomial
import ThomsonNine.RationalListPolynomial

noncomputable section
namespace ThomsonNine.IntegerListPolynomial
open Polynomial
theorem append (l m : List ℤ) : realPolynomial (l++m)=realPolynomial l+X^l.length*realPolynomial m := by
  induction l with
  | nil => simp [realPolynomial,ListPolynomial.polynomial]
  | cons a l ih =>
    change C (a : ℝ)+X*realPolynomial (l++m)=
      (C (a : ℝ)+X*realPolynomial l)+X^(l.length+1)*realPolynomial m
    rw [ih,pow_succ]
    ring
theorem zeroes (n : ℕ) : realPolynomial (List.replicate n 0)=0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ,cons,ih];simp
theorem rational_map (l : List ℤ) : RationalListPolynomial.realPolynomial (l.map (fun z : ℤ => (z : ℚ)))=realPolynomial l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons,RationalListPolynomial.cons,cons,ih,Rat.cast_intCast]
end ThomsonNine.IntegerListPolynomial
