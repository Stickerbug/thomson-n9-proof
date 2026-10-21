/-
Interval enclosures of Bernstein basis functions.

For a parameter interval `Iu` inside `[0,1]`, `bernInterval n i Iu` encloses the
basis value `C(n,i) z^i (1-z)^(n-i)` for every `z ∈ Iu`.  This is the atomic
building block of the certificate evaluator: coefficient enclosures are
multiplied into these nonnegative basis enclosures with `mulMixed`.
-/
import ThomsonNine.IntervalMul
import ThomsonNine.LeafSemantics
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

namespace ThomsonNine
namespace Interval
namespace RatInterval

open ThomsonNine.Semantics

/-- The interval `1 - I`. -/
def oneMinus (I : RatInterval) : RatInterval := sub (const 1) I

theorem oneMinus_lo_nonneg {I : RatInterval} (h : I.hi ≤ 1) : 0 ≤ (oneMinus I).lo := by
  have h' : (0 : ℚ) ≤ 1 - I.hi := by linarith
  simpa [oneMinus, sub, add, neg, const] using h'

/-- Enclosure of the `i`-th Bernstein basis function of degree `n` on an
interval inside `[0,1]`. -/
def bernInterval (n i : ℕ) (Iu : RatInterval) (hlo : 0 ≤ Iu.lo) (hhi : Iu.hi ≤ 1) :
    RatInterval :=
  scale ((n.choose i : ℚ)) (by positivity)
    (mulNonneg (powNonneg Iu hlo i) (powNonneg (oneMinus Iu) (oneMinus_lo_nonneg hhi) (n - i))
      (pow_nonneg hlo i)
      (pow_nonneg (oneMinus_lo_nonneg hhi) (n - i)))

/-- Soundness: the Bernstein basis value lies in `bernInterval`. -/
theorem mem_bernInterval (n i : ℕ) (Iu : RatInterval) (hlo : 0 ≤ Iu.lo) (hhi : Iu.hi ≤ 1)
    {z : ℝ} (hz : Iu.mem z) :
    (bernInterval n i Iu hlo hhi).mem (bernstein n i z) := by
  have hOne : 0 ≤ (oneMinus Iu).lo := oneMinus_lo_nonneg hhi
  have hmul : (mulNonneg (powNonneg Iu hlo i) (powNonneg (oneMinus Iu) hOne (n - i))
      (pow_nonneg hlo i) (pow_nonneg hOne (n - i))).mem
      (z ^ i * (1 - z) ^ (n - i)) :=
    mem_mulNonneg (pow_nonneg hlo i) (pow_nonneg hOne (n - i))
      (mem_powNonneg hlo i hz) (mem_powNonneg hOne (n - i) (mem_sub (show (const (1:ℚ)).mem (1:ℝ) from by simpa using (mem_const (1:ℚ))) hz))
  have hscale := mem_scale (by positivity : (0 : ℚ) ≤ (n.choose i : ℚ)) hmul
  have hcast : (((n.choose i : ℚ)) : ℝ) = (n.choose i : ℝ) := by push_cast; rfl
  simpa [bernInterval, bernstein, hcast, mul_assoc] using hscale

/-- The lower endpoint of a Bernstein basis enclosure is nonnegative. -/
theorem bernInterval_lo_nonneg (n i : ℕ) (Iu : RatInterval) (hlo : 0 ≤ Iu.lo) (hhi : Iu.hi ≤ 1) :
    0 ≤ (bernInterval n i Iu hlo hhi).lo := by
  have hOne : 0 ≤ (oneMinus Iu).lo := oneMinus_lo_nonneg hhi
  show (0 : ℚ) ≤ ((n.choose i : ℚ)) * (Iu.lo ^ i * (oneMinus Iu).lo ^ (n - i))
  exact mul_nonneg (by positivity)
    (mul_nonneg (pow_nonneg hlo i) (pow_nonneg hOne (n - i)))

/-- Enclosure of a signed coefficient times three nonnegative basis values. -/
theorem mem_mulMixed3 {I J K : RatInterval} (hJ : 0 ≤ J.lo) (hK : 0 ≤ K.lo) {x y z : ℝ}
    (hx : I.mem x) (hy : J.mem y) (hz : K.mem z) :
    (mulMixed (mulMixed I J hJ) K hK).mem (x * y * z) := by
  have h1 : (mulMixed I J hJ).mem (x * y) := mem_mulMixed hJ hx hy
  have h2 := mem_mulMixed hK h1 hz
  simpa only [mul_assoc] using h2

end RatInterval
end Interval
end ThomsonNine
