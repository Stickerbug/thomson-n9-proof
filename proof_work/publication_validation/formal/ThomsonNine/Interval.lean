/-
Verified interval-arithmetic layer with rational endpoints.

This module starts the numeric-certificate route: the interval certificates of the
nine-point proof candidate are finite lists of rational enclosures, and the claims
that certain Bernstein coefficients are positive are established by evaluating the
enclosures with outward rounding.  Everything here is exact: intervals have rational
endpoints, membership is a statement about real numbers, and every arithmetic
operation comes with a soundness theorem.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Positivity

namespace ThomsonNine
namespace Interval

/-- A closed interval with rational endpoints. -/
structure RatInterval where
  lo : ℚ
  hi : ℚ
  h : lo ≤ hi

namespace RatInterval

/-- A real number lies in the interval. -/
def mem (I : RatInterval) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

/-- The degenerate interval containing a single rational number. -/
def const (q : ℚ) : RatInterval := ⟨q, q, le_rfl⟩

theorem mem_const (q : ℚ) : (const q).mem ((q : ℝ)) := ⟨le_rfl, le_rfl⟩

/-- Outward-rounded addition. -/
def add (I J : RatInterval) : RatInterval :=
  ⟨I.lo + J.lo, I.hi + J.hi, by linarith [I.h, J.h]⟩

theorem mem_add {I J : RatInterval} {x y : ℝ} (hx : I.mem x) (hy : J.mem y) :
    (add I J).mem (x + y) := by
  constructor
  · show (((I.lo + J.lo : ℚ)) : ℝ) ≤ x + y
    push_cast
    linarith [hx.1, hy.1]
  · show x + y ≤ (((I.hi + J.hi : ℚ)) : ℝ)
    push_cast
    linarith [hx.2, hy.2]

/-- Outward-rounded negation. -/
def neg (I : RatInterval) : RatInterval :=
  ⟨-I.hi, -I.lo, by linarith [I.h]⟩

theorem mem_neg {I : RatInterval} {x : ℝ} (hx : I.mem x) : (neg I).mem (-x) := by
  constructor
  · show (((-I.hi : ℚ)) : ℝ) ≤ -x
    push_cast
    linarith [hx.2]
  · show -x ≤ (((-I.lo : ℚ)) : ℝ)
    push_cast
    linarith [hx.1]

/-- Outward-rounded subtraction. -/
def sub (I J : RatInterval) : RatInterval := add I (neg J)

theorem mem_sub {I J : RatInterval} {x y : ℝ} (hx : I.mem x) (hy : J.mem y) :
    (sub I J).mem (x - y) := by
  simpa only [sub, sub_eq_add_neg] using mem_add hx (mem_neg hy)

/-- Multiplication of an interval by a nonnegative rational. -/
def scale (c : ℚ) (hc : 0 ≤ c) (I : RatInterval) : RatInterval :=
  ⟨c * I.lo, c * I.hi, mul_le_mul_of_nonneg_left I.h hc⟩

theorem mem_scale {c : ℚ} (hc : 0 ≤ c) {I : RatInterval} {x : ℝ} (hx : I.mem x) :
    (scale c hc I).mem ((c : ℝ) * x) := by
  have hc' : (0 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  constructor
  · show (((c * I.lo : ℚ)) : ℝ) ≤ (c : ℝ) * x
    push_cast
    nlinarith [hx.1]
  · show (c : ℝ) * x ≤ (((c * I.hi : ℚ)) : ℝ)
    push_cast
    nlinarith [hx.2]

/-- Product of two intervals with nonnegative lower bounds (all of both intervals
is then nonnegative). -/
def mulNonneg (I J : RatInterval) (hI : 0 ≤ I.lo) (hJ : 0 ≤ J.lo) : RatInterval :=
  ⟨I.lo * J.lo, I.hi * J.hi, by nlinarith [I.h, J.h, hI, hJ]⟩

theorem mem_mulNonneg {I J : RatInterval} {x y : ℝ} (hI : 0 ≤ I.lo) (hJ : 0 ≤ J.lo)
    (hx : I.mem x) (hy : J.mem y) : (mulNonneg I J hI hJ).mem (x * y) := by
  have hI' : (0 : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast hI
  have hJ' : (0 : ℝ) ≤ (J.lo : ℝ) := by exact_mod_cast hJ
  have hx0 : (0 : ℝ) ≤ x := le_trans hI' hx.1
  have hy0 : (0 : ℝ) ≤ y := le_trans hJ' hy.1
  have hhi0 : (0 : ℝ) ≤ (I.hi : ℝ) := le_trans hI' (by exact_mod_cast I.h)
  constructor
  · show (((I.lo * J.lo : ℚ)) : ℝ) ≤ x * y
    push_cast
    exact mul_le_mul hx.1 hy.1 hJ' hx0
  · show x * y ≤ (((I.hi * J.hi : ℚ)) : ℝ)
    push_cast
    exact mul_le_mul hx.2 hy.2 hy0 hhi0

/-- Nonnegative integer power of an interval whose lower bound is nonnegative. -/
def powNonneg (I : RatInterval) (hI : 0 ≤ I.lo) (n : ℕ) : RatInterval :=
  ⟨I.lo ^ n, I.hi ^ n, pow_le_pow_left₀ hI I.h n⟩

theorem mem_powNonneg {I : RatInterval} (hI : 0 ≤ I.lo) (n : ℕ) {x : ℝ} (hx : I.mem x) :
    (powNonneg I hI n).mem (x ^ n) := by
  have hI' : (0 : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast hI
  have hx0 : (0 : ℝ) ≤ x := le_trans hI' hx.1
  constructor
  · show (((I.lo ^ n : ℚ)) : ℝ) ≤ x ^ n
    rw [show (((I.lo ^ n : ℚ)) : ℝ) = (I.lo : ℝ) ^ n by rw [Rat.cast_pow]]
    exact pow_le_pow_left₀ hI' hx.1 n
  · show x ^ n ≤ (((I.hi ^ n : ℚ)) : ℝ)
    rw [show (((I.hi ^ n : ℚ)) : ℝ) = (I.hi : ℝ) ^ n by rw [Rat.cast_pow]]
    exact pow_le_pow_left₀ hx0 hx.2 n

/-- If the lower bound is nonnegative, every member is nonnegative. -/
theorem nonneg_of_lo {I : RatInterval} (h : 0 ≤ I.lo) {x : ℝ} (hx : I.mem x) : 0 ≤ x :=
  le_trans (by exact_mod_cast h) hx.1

end RatInterval
end Interval
end ThomsonNine
