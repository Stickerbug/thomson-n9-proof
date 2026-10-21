import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace ThomsonNine.TaylorTen

noncomputable def taylorP (z : ℝ) : ℝ :=
    (1 / 1 : ℝ) +
    (1 / 2 : ℝ) * z^1 +
    (3 / 8 : ℝ) * z^2 +
    (5 / 16 : ℝ) * z^3 +
    (35 / 128 : ℝ) * z^4 +
    (63 / 256 : ℝ) * z^5 +
    (231 / 1024 : ℝ) * z^6 +
    (429 / 2048 : ℝ) * z^7 +
    (6435 / 32768 : ℝ) * z^8 +
    (12155 / 65536 : ℝ) * z^9 +
    (46189 / 262144 : ℝ) * z^10

noncomputable def taylorR (z : ℝ) : ℝ :=
    (88179 / 262144 : ℝ) +
    (323323 / 2097152 : ℝ) * z^1 +
    (223839 / 2097152 : ℝ) * z^2 +
    (692835 / 8388608 : ℝ) * z^3 +
    (2263261 / 33554432 : ℝ) * z^4 +
    (61108047 / 1073741824 : ℝ) * z^5 +
    (13180167 / 268435456 : ℝ) * z^6 +
    (46235189 / 1073741824 : ℝ) * z^7 +
    (328513185 / 8589934592 : ℝ) * z^8 +
    (2357994639 / 68719476736 : ℝ) * z^9 +
    (2133423721 / 68719476736 : ℝ) * z^10

theorem exact_polynomial_identity (z : ℝ) :
    (1-z) * taylorP z ^ 2 + z^11 * taylorR z = 1 := by
  unfold taylorP taylorR
  ring

theorem partial_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ taylorP z := by
  unfold taylorP
  positivity

theorem remainder_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ taylorR z := by
  unfold taylorR
  positivity

/-- The degree-ten binomial lower bound, proved by an exact polynomial identity. -/
theorem partial_le_inverse_sqrt {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) :
    taylorP z ≤ (Real.sqrt (1-z))⁻¹ := by
  have hp : 0 < 1-z := sub_pos.mpr hz1
  have hs : 0 < Real.sqrt (1-z) := Real.sqrt_pos.mpr hp
  have hsq : (1-z) * taylorP z ^ 2 ≤ 1 := by
    calc
      (1-z) * taylorP z ^ 2 ≤ (1-z) * taylorP z ^ 2 + z^11 * taylorR z :=
        le_add_of_nonneg_right (mul_nonneg (pow_nonneg hz 11) (remainder_nonneg hz))
      _ = 1 := exact_polynomial_identity z
  have hx : (taylorP z * Real.sqrt (1-z))^2 ≤ 1 := by
    calc
      (taylorP z * Real.sqrt (1-z))^2 = (1-z) * taylorP z^2 := by
        rw [mul_pow, Real.sq_sqrt (le_of_lt hp)]
        ring
      _ ≤ 1 := hsq
  have hm : taylorP z * Real.sqrt (1-z) ≤ 1 := by nlinarith
  simpa only [one_div] using (le_div_iff₀ hs).mpr hm

/-- No sign assumption on h is needed for this square-bound implication. -/
theorem le_inverse_sqrt_of_square_bound {h a : ℝ} (ha : 0 < a)
    (hb : a*h^2 ≤ 1) : h ≤ (Real.sqrt a)⁻¹ := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hx : (h * Real.sqrt a)^2 ≤ 1 := by
    calc
      (h * Real.sqrt a)^2 = a*h^2 := by
        rw [mul_pow, Real.sq_sqrt (le_of_lt ha)]
        ring
      _ ≤ 1 := hb
  have hm : h * Real.sqrt a ≤ 1 := by nlinarith
  simpa only [one_div] using (le_div_iff₀ hs).mpr hm

/-- A finite polynomial factorization can replace the analytic Hermite taylorR lemma. -/
theorem minorant_of_algebraic_factor {h x w q : ℝ} (hx : x < 1)
    (hw : 0 ≤ w) (hq : 0 ≤ q)
    (hid : 1-(2-2*x)*h^2 = w*q) : h ≤ (Real.sqrt (2-2*x))⁻¹ := by
  have ha : 0 < 2-2*x := by nlinarith
  apply le_inverse_sqrt_of_square_bound ha
  have hnonneg : 0 ≤ w*q := mul_nonneg hw hq
  nlinarith

end ThomsonNine.TaylorTen
