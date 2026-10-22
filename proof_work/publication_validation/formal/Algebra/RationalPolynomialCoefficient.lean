import ThomsonNine.RationalListPolynomial

noncomputable section
namespace ThomsonNine.RationalListPolynomial
open Polynomial
theorem coefficient (l : List ℚ) (n : ℕ) :
    (realPolynomial l).coeff n=(((l[n]?).getD 0 : ℚ) : ℝ) := by
  induction l generalizing n with
  | nil => simp
  | cons a l ih => cases n <;> simp [cons,ih]
end ThomsonNine.RationalListPolynomial
