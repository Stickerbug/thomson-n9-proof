import Algebra.ExactPolynomial

noncomputable section
namespace ThomsonNine.ExactPolynomial
open Polynomial ThomsonNine.RationalListPolynomial
def compose : List ℚ → List ℚ → List ℚ
  | [],_ => []
  | c::l,a => add [c] (mul a (compose l a))
theorem compose_sound (l a : List ℚ) : realPolynomial (compose l a)=(realPolynomial l).comp (realPolynomial a) := by
  induction l with
  | nil => simp [compose]
  | cons c l ih =>
    rw [compose,add_sound,mul_sound,ih]
    simp only [RationalListPolynomial.cons,RationalListPolynomial.nil,mul_zero,add_zero,add_comp,mul_comp,C_comp,X_comp]
end ThomsonNine.ExactPolynomial
