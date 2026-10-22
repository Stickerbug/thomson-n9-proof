import ThomsonNine.Interval
import ThomsonNine.LeafSemantics

/-! Scalar LDL semantics for the actual local certificates.

The checker computes P = W H Wᵀ, then P = L D Lᵀ, with W exact unit lower
triangular and L, D enclosed by intervals. Thus H's quadratic form is evaluated
using Lᵀ W⁻ᵀ, not L Wᵀ. The entry identities below are proved algebraically;
interval enclosures of the real LDL pivots remain explicit premises. This file
does not prove that the exported polynomial has the certified Hessian.
-/

namespace ThomsonNine.LocalLDL

open ThomsonNine.Interval

/-- `vᵀ L D Lᵀ v` for unit lower triangular `L`. -/
def quadratic (d1 d2 d3 l21 l31 l32 x y z : ℝ) : ℝ :=
  d1 * (x + l21 * y + l31 * z) ^ 2 +
    d2 * (y + l32 * z) ^ 2 + d3 * z ^ 2

theorem quadratic_nonneg (d1 d2 d3 l21 l31 l32 x y z : ℝ)
    (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) (hd3 : 0 ≤ d3) :
    0 ≤ quadratic d1 d2 d3 l21 l31 l32 x y z := by
  exact add_nonneg
    (add_nonneg (mul_nonneg hd1 (sq_nonneg _)) (mul_nonneg hd2 (sq_nonneg _)))
    (mul_nonneg hd3 (sq_nonneg _))

/-- Symmetric 3 by 3 quadratic form, with six independent entries. -/
def symmetricQuadratic (a b c d e f x y z : ℝ) : ℝ :=
  a * x ^ 2 + 2 * b * x * y + 2 * c * x * z +
    d * y ^ 2 + 2 * e * y * z + f * z ^ 2

/-- Entrywise LDL identities imply the correct sum of squares. -/
theorem quadratic_eq_of_entries (a b c d e f d1 d2 d3 l21 l31 l32 : ℝ)
    (ha : a = d1) (hb : b = l21 * d1) (hc : c = l31 * d1)
    (hd : d = l21 ^ 2 * d1 + d2)
    (he : e = l31 * l21 * d1 + l32 * d2)
    (hf : f = l31 ^ 2 * d1 + l32 ^ 2 * d2 + d3) (x y z : ℝ) :
    symmetricQuadratic a b c d e f x y z = quadratic d1 d2 d3 l21 l31 l32 x y z := by
  rw [ha, hb, hc, hd, he, hf]
  unfold symmetricQuadratic quadratic
  ring

/-- Exact certificate data: the L intervals are metadata, pivot positivity drives PSD. -/
structure LDL3Cert where
  d1 : RatInterval
  d2 : RatInterval
  d3 : RatInterval
  l21 : RatInterval
  l31 : RatInterval
  l32 : RatInterval
  w21 : ℚ
  w31 : ℚ
  w32 : ℚ
  hd1 : 0 < d1.lo
  hd2 : 0 < d2.lo
  hd3 : 0 < d3.lo

theorem positive_of_mem {I : RatInterval} (hI : 0 < I.lo) {d : ℝ}
    (hd : I.mem d) : 0 < d := by
  have hlo : (0 : ℝ) < (I.lo : ℝ) := by exact_mod_cast hI
  exact lt_of_lt_of_le hlo hd.1

/-- L can be arbitrary: only the pivots need interval membership for this implication. -/
theorem LDL3Cert.sound (cert : LDL3Cert) {d1 d2 d3 : ℝ}
    (h1 : cert.d1.mem d1) (h2 : cert.d2.mem d2) (h3 : cert.d3.mem d3)
    (l21 l31 l32 x y z : ℝ) :
    0 ≤ quadratic d1 d2 d3 l21 l31 l32 x y z :=
  quadratic_nonneg _ _ _ _ _ _ _ _ _
    (le_of_lt (positive_of_mem cert.hd1 h1))
    (le_of_lt (positive_of_mem cert.hd2 h2))
    (le_of_lt (positive_of_mem cert.hd3 h3))

/-- `W⁻ᵀ v` for exact unit lower triangular W. -/
def preconditionedHessianQuadratic (cert : LDL3Cert)
    (d1 d2 d3 l21 l31 l32 : ℝ) (x y z : ℝ) : ℝ :=
  quadratic d1 d2 d3 l21 l31 l32
    (x - (cert.w21 : ℝ) * y + ((cert.w21 : ℝ) * cert.w32 - cert.w31) * z)
    (y - (cert.w32 : ℝ) * z) z

/-- Invert the congruence P = W H Wᵀ at the level of quadratic forms. -/
theorem congruence_nonneg (Q P : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ)
    (hP : ∀ x y z, P x y z = Q (x + a * y + b * z) (y + c * z) z)
    (hpos : ∀ x y z, 0 ≤ P x y z) (x y z : ℝ) : 0 ≤ Q x y z := by
  have h := hpos (x - a * y + (a * c - b) * z) (y - c * z) z
  rw [hP] at h
  have hx : x - a * y + (a * c - b) * z + a * (y - c * z) + b * z = x := by ring
  have hy : y - c * z + c * z = y := by ring
  rwa [hx, hy] at h

/-- An explicit factorization premise is still required for the actual Hessian. -/
theorem hessian_quadratic_nonneg (cert : LDL3Cert) {d1 d2 d3 : ℝ}
    (h1 : cert.d1.mem d1) (h2 : cert.d2.mem d2) (h3 : cert.d3.mem d3)
    (l21 l31 l32 : ℝ) (Q : ℝ → ℝ → ℝ → ℝ)
    (hfactor : ∀ x y z, Q x y z =
      preconditionedHessianQuadratic cert d1 d2 d3 l21 l31 l32 x y z)
    (x y z : ℝ) : 0 ≤ Q x y z := by
  rw [hfactor]
  exact cert.sound h1 h2 h3 l21 l31 l32 _ _ _

/-- The boundary graph has a 2 by 2 Hessian. -/
def quadratic2 (d1 d2 l21 x y : ℝ) : ℝ :=
  d1 * (x + l21 * y) ^ 2 + d2 * y ^ 2

structure LDL2Cert where
  d1 : RatInterval
  d2 : RatInterval
  l21 : RatInterval
  w21 : ℚ
  hd1 : 0 < d1.lo
  hd2 : 0 < d2.lo

theorem LDL2Cert.sound (cert : LDL2Cert) {d1 d2 : ℝ}
    (h1 : cert.d1.mem d1) (h2 : cert.d2.mem d2) (l21 x y : ℝ) :
    0 ≤ quadratic2 d1 d2 l21 x y := by
  exact add_nonneg
    (mul_nonneg (le_of_lt (positive_of_mem cert.hd1 h1)) (sq_nonneg _))
    (mul_nonneg (le_of_lt (positive_of_mem cert.hd2 h2)) (sq_nonneg _))

theorem quadratic2_eq_of_entries (a b c d1 d2 l21 x y : ℝ)
    (ha : a = d1) (hb : b = l21 * d1) (hc : c = l21 ^ 2 * d1 + d2) :
    a * x ^ 2 + 2 * b * x * y + c * y ^ 2 = quadratic2 d1 d2 l21 x y := by
  rw [ha, hb, hc]
  unfold quadratic2
  ring

theorem congruence2_nonneg (Q P : ℝ → ℝ → ℝ) (a : ℝ)
    (hP : ∀ x y, P x y = Q (x + a * y) y)
    (hpos : ∀ x y, 0 ≤ P x y) (x y : ℝ) : 0 ≤ Q x y := by
  have h := hpos (x - a * y) y
  rw [hP] at h
  have hx : x - a * y + a * y = x := by ring
  rwa [hx] at h

/-- Boundary multipliers must be nonnegative. -/
theorem boundary_residual_nonneg {R G lambda : ℝ}
    (hlambda : 0 ≤ lambda) (hG : 0 ≤ G) (hcompensated : 0 ≤ R - lambda * G) :
    0 ≤ R := ThomsonNine.Semantics.boundary_multiplier hlambda hG hcompensated

end ThomsonNine.LocalLDL
