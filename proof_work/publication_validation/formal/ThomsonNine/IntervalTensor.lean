/-
Certificate semantics for Bernstein tensors from rational interval enclosures.

This is the leaf-checking principle of the numeric certificate route: if every
Bernstein coefficient of a ternary tensor is known to lie in a rational interval
whose lower bound is nonnegative, then the tensor is nonnegative on the whole unit
cube (indeed everywhere).  The numeric checker verifies exactly this: the lower
bounds are rationals, and the positivity test is a rational comparison.
-/
import ThomsonNine.Interval
import ThomsonNine.LeafSemantics
import Mathlib.Tactic.Linarith

namespace ThomsonNine
namespace Interval

open ThomsonNine.Semantics

/-- If each coefficient of a ternary Bernstein tensor is enclosed by a rational
interval with nonnegative lower bound, the tensor is nonnegative everywhere. -/
theorem tensor_nonneg_of_coeff_intervals {n : ℕ}
    (C : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → RatInterval)
    (c : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℝ)
    (hc : ∀ i j k, (C i j k).mem (c i j k))
    (hlo : ∀ i j k, 0 ≤ (C i j k).lo)
    {u v t : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (hv : 0 ≤ v) (hv1 : v ≤ 1)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) : 0 ≤ tensor n c u v t := by
  refine tensor_nonneg n c (fun i j k => ?_) hu hu1 hv hv1 ht ht1
  exact RatInterval.nonneg_of_lo (hlo i j k) (hc i j k)

end Interval
end ThomsonNine
