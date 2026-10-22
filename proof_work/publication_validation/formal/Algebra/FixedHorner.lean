import ThomsonNine.RationalListPolynomial
import Mathlib.Algebra.Order.Floor.Ring

noncomputable section
namespace ThomsonNine.FixedInterval
open ThomsonNine.RationalListPolynomial

def rational (s : ℤ) (q : ℚ) : Bounds := ⟨⌊(s : ℚ)*q⌋,⌈(s : ℚ)*q⌉⟩
theorem rational_mem (s : ℤ) (q : ℚ) : Mem s (rational s q) (q : ℝ) := by
  constructor
  · change ((⌊(s : ℚ)*q⌋ : ℤ) : ℝ) ≤ (s : ℝ)*(q : ℝ)
    exact_mod_cast (Int.floor_le ((s : ℚ)*q))
  · change (s : ℝ)*(q : ℝ) ≤ ((⌈(s : ℚ)*q⌉ : ℤ) : ℝ)
    exact_mod_cast (Int.le_ceil ((s : ℚ)*q))

def horner (s : ℤ) (x : Bounds) : List ℚ → Bounds
  | [] => zero
  | a::l => add (rational s a) (mul s x (horner s x l))

theorem horner_mem {s : ℤ} (hs : 0<s) {x : Bounds} {a : ℝ} (hx : Mem s x a)
    (l : List ℚ) : Mem s (horner s x l) ((realPolynomial l).eval a) := by
  induction l with
  | nil => simpa [horner] using mem_zero s
  | cons b l ih =>
    simpa only [horner,RationalListPolynomial.cons,Polynomial.eval_add,
      Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X] using
      mem_add (rational_mem s b) (mem_mul hs hx ih)
end ThomsonNine.FixedInterval
