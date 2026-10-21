/-
Mixed-sign interval multiplication by a nonnegative interval.

The certificate evaluation multiplies a signed coefficient enclosure by a
nonnegative Bernstein-basis enclosure.  This module provides that operation with
its soundness theorem, splitting on the sign of the left factor.
-/
import ThomsonNine.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

namespace ThomsonNine
namespace Interval
namespace RatInterval

/-- Product of an arbitrary interval with a nonnegative interval. -/
def mulMixed (I J : RatInterval) (hJ : 0 ≤ J.lo) : RatInterval :=
  if h1 : 0 ≤ I.lo then
    mulNonneg I J h1 hJ
  else if h2 : I.hi ≤ 0 then
    ⟨I.lo * J.hi, I.hi * J.lo, by
      have hJhi : 0 ≤ J.hi := le_trans hJ J.h
      have s1 : I.lo * J.hi ≤ I.hi * J.hi := mul_le_mul_of_nonneg_right I.h hJhi
      have s2 : I.hi * J.hi ≤ I.hi * J.lo := mul_le_mul_of_nonpos_left J.h h2
      exact le_trans s1 s2⟩
  else
    ⟨I.lo * J.hi, I.hi * J.hi, by
      have hJhi : 0 ≤ J.hi := le_trans hJ J.h
      exact mul_le_mul_of_nonneg_right I.h hJhi⟩

/-- Soundness of `mulMixed`. -/
theorem mem_mulMixed {I J : RatInterval} (hJ : 0 ≤ J.lo) {x y : ℝ}
    (hx : I.mem x) (hy : J.mem y) : (mulMixed I J hJ).mem (x * y) := by
  have hy0 : (0 : ℝ) ≤ y := le_trans (by exact_mod_cast hJ) hy.1
  unfold mulMixed
  by_cases h1 : 0 ≤ I.lo
  · simp only [dif_pos h1]
    exact mem_mulNonneg h1 hJ hx hy
  · by_cases h2 : I.hi ≤ 0
    · simp only [dif_neg h1, dif_pos h2]
      have hIlo0 : (I.lo : ℝ) ≤ 0 :=
        le_trans hx.1 (le_trans hx.2 (by exact_mod_cast h2))
      have hIhi0 : (I.hi : ℝ) ≤ 0 := by exact_mod_cast h2
      constructor
      · show (((I.lo * J.hi : ℚ)) : ℝ) ≤ x * y
        push_cast
        have s1 : (I.lo : ℝ) * (J.hi : ℝ) ≤ (I.lo : ℝ) * y :=
          mul_le_mul_of_nonpos_left hy.2 hIlo0
        have s2 : (I.lo : ℝ) * y ≤ x * y := mul_le_mul_of_nonneg_right hx.1 hy0
        linarith
      · show x * y ≤ (((I.hi * J.lo : ℚ)) : ℝ)
        push_cast
        have s1 : x * y ≤ (I.hi : ℝ) * y := mul_le_mul_of_nonneg_right hx.2 hy0
        have s2 : (I.hi : ℝ) * y ≤ (I.hi : ℝ) * (J.lo : ℝ) :=
          mul_le_mul_of_nonpos_left hy.1 hIhi0
        linarith
    · simp only [dif_neg h1, dif_neg h2]
      have hIhi0 : (0 : ℝ) < (I.hi : ℝ) := by
        have h : ¬ (I.hi : ℝ) ≤ 0 := by exact_mod_cast h2
        linarith
      have hIlo0 : (I.lo : ℝ) ≤ 0 := by
        have h : I.lo ≤ 0 := le_of_lt (not_le.mp h1)
        exact_mod_cast h
      constructor
      · show (((I.lo * J.hi : ℚ)) : ℝ) ≤ x * y
        push_cast
        have s1 : (I.lo : ℝ) * (J.hi : ℝ) ≤ (I.lo : ℝ) * y :=
          mul_le_mul_of_nonpos_left hy.2 hIlo0
        have s2 : (I.lo : ℝ) * y ≤ x * y := mul_le_mul_of_nonneg_right hx.1 hy0
        linarith
      · show x * y ≤ (((I.hi * J.hi : ℚ)) : ℝ)
        push_cast
        have s1 : x * y ≤ (I.hi : ℝ) * y := mul_le_mul_of_nonneg_right hx.2 hy0
        have s2 : (I.hi : ℝ) * y ≤ (I.hi : ℝ) * (J.hi : ℝ) :=
          mul_le_mul_of_nonneg_left hy.2 (le_of_lt hIhi0)
        linarith

end RatInterval
end Interval
end ThomsonNine
