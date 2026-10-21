import ThomsonNine.LocalLDLSemantics
import Mathlib.Analysis.Convex.Deriv

/-! Analytic bridge for local certificates.

The segment derivatives, exact contact and LDL memberships are explicit premises.
This proves the implication from those premises to nonnegativity; it does not
assert them for the frozen residual polynomial or its boundary graph.
-/

namespace ThomsonNine.LocalLDL

/-- A convex scalar restriction with zero value and derivative at its left endpoint
is nonnegative on the whole unit segment, including both endpoints. -/
theorem segment_nonneg_of_convex {f : ℝ → ℝ}
    (hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f)
    (hzero : f 0 = 0) (hderiv : HasDerivAt f 0 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f t := by
  intro t ht
  rcases lt_or_eq_of_le ht.1 with hpos | hzero_t
  · have hs : 0 ≤ slope f 0 t :=
      hconv.le_slope_of_hasDerivAt (by constructor <;> norm_num) ht hpos hderiv
    rw [slope_def_field] at hs
    have hn := (le_div_iff₀ (sub_pos.mpr hpos)).mp hs
    simpa [hzero] using hn
  · simpa [← hzero_t, hzero]

/-- Nonnegative second derivative, with explicit derivative witnesses. -/
theorem segment_nonneg_of_second_derivative {f f' f'' : ℝ → ℝ}
    (hc : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hd : ∀ s ∈ interior (Set.Icc (0 : ℝ) 1), HasDerivAt f (f' s) s)
    (hdd : ∀ s ∈ interior (Set.Icc (0 : ℝ) 1), HasDerivAt f' (f'' s) s)
    (hsecond : ∀ s ∈ interior (Set.Icc (0 : ℝ) 1), 0 ≤ f'' s)
    (hzero : f 0 = 0) (hderiv : HasDerivAt f 0 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f t := by
  apply segment_nonneg_of_convex _ hzero hderiv
  exact convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1) hc
    (fun s hs => (hd s hs).hasDerivWithinAt)
    (fun s hs => (hdd s hs).hasDerivWithinAt) hsecond

/-- Interior LDL certificate along one segment, with the chain rule made explicit
as the identity for the actual scalar second derivative `f''`. -/
theorem segment_nonneg_of_ldl3 (cert : LDL3Cert) {f f' f'' : ℝ → ℝ}
    (hc : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hd : ∀ s ∈ interior (Set.Icc (0 : ℝ) 1), HasDerivAt f (f' s) s)
    (hdd : ∀ s ∈ interior (Set.Icc (0 : ℝ) 1), HasDerivAt f' (f'' s) s)
    (d1 d2 d3 l21 l31 l32 : ℝ → ℝ) (x y z : ℝ)
    (h1 : ∀ s ∈ interior (Set.Icc (0 : ℝ) 1), cert.d1.mem (d1 s))
    (h2 : ∀ s ∈ interior (Set.Icc (0 : ℝ) 1), cert.d2.mem (d2 s))
    (h3 : ∀ s ∈ interior (Set.Icc (0 : ℝ) 1), cert.d3.mem (d3 s))
    (hfactor : ∀ s ∈ interior (Set.Icc (0 : ℝ) 1), f'' s =
      preconditionedHessianQuadratic cert (d1 s) (d2 s) (d3 s)
        (l21 s) (l31 s) (l32 s) x y z)
    (hzero : f 0 = 0) (hderiv : HasDerivAt f 0 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f t := by
  apply segment_nonneg_of_second_derivative hc hd hdd _ hzero hderiv
  intro s hs
  rw [hfactor s hs]
  exact cert.sound (h1 s hs) (h2 s hs) (h3 s hs) (l21 s) (l31 s) (l32 s) _ _ _

/-- Boundary graph LDL certificate: the graph restriction has dimension two. -/
theorem segment_nonneg_of_ldl2 (cert : LDL2Cert) {f f' f'' : ℝ → ℝ}
    (hc : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hd : ∀ s ∈ interior (Set.Icc (0 : ℝ) 1), HasDerivAt f (f' s) s)
    (hdd : ∀ s ∈ interior (Set.Icc (0 : ℝ) 1), HasDerivAt f' (f'' s) s)
    (d1 d2 l21 : ℝ → ℝ) (x y : ℝ)
    (h1 : ∀ s ∈ interior (Set.Icc (0 : ℝ) 1), cert.d1.mem (d1 s))
    (h2 : ∀ s ∈ interior (Set.Icc (0 : ℝ) 1), cert.d2.mem (d2 s))
    (hfactor : ∀ s ∈ interior (Set.Icc (0 : ℝ) 1), f'' s =
      quadratic2 (d1 s) (d2 s) (l21 s) (x - (cert.w21 : ℝ) * y) y)
    (hzero : f 0 = 0) (hderiv : HasDerivAt f 0 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f t := by
  apply segment_nonneg_of_second_derivative hc hd hdd _ hzero hderiv
  intro s hs
  rw [hfactor s hs]
  exact cert.sound (h1 s hs) (h2 s hs) (l21 s) _ _

/-- Extend nonnegativity on the lower Gram graph to a feasible point above it.
The interval D must include BOTH the graph value b and the point u; the original
sourcebox alone need not do so. -/
theorem nonneg_above_boundary {D : Set ℝ} {f f' : ℝ → ℝ} {b u : ℝ}
    (hD : Convex ℝ D) (hc : ContinuousOn f D)
    (hd : ∀ s ∈ interior D, HasDerivAt f (f' s) s)
    (hpos : ∀ s ∈ interior D, 0 ≤ f' s)
    (hb : b ∈ D) (hu : u ∈ D) (hbu : b ≤ u) (hboundary : 0 ≤ f b) :
    0 ≤ f u := by
  have hm : MonotoneOn f D := monotoneOn_of_hasDerivWithinAt_nonneg hD hc
    (fun s hs => (hd s hs).hasDerivWithinAt) hpos
  exact le_trans hboundary (hm hb hu hbu)

end ThomsonNine.LocalLDL
