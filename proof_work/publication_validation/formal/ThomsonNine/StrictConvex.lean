import ThomsonNine.Minimum
import Mathlib.Analysis.Convex.Deriv

open ThomsonNine
open ThomsonNine.Family

namespace ThomsonNine.Family

/-! Strict convexity of the family energy on (0,1).

The second derivative is strictly positive there, so `strictConvexOn_of_deriv2_pos`
applies.  This is a structural companion to `exists_unique_familyEnergy_min`. -/

theorem strictConvexOn_familyEnergy :
    StrictConvexOn ℝ (Set.Ioo (0 : ℝ) 1) familyEnergy := by
  refine strictConvexOn_of_deriv2_pos (convex_Ioo (0 : ℝ) 1) ?_ ?_
  · exact (differentiableOn_familyEnergy.mono (by intro x hx; exact hx)).continuousOn
  · intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := by simpa only [interior_Ioo] using hx
    have hfun : deriv familyEnergy =ᶠ[nhds x] familyEnergyDeriv := by
      filter_upwards [Ioo_mem_nhds hx'.1 hx'.2] with y hy
      exact (hasDerivAt_familyEnergy y hy.1 hy.2).deriv
    have h2 : HasDerivAt (deriv familyEnergy) (familyEnergyDeriv2 x) x :=
      (hasDerivAt_familyEnergyDeriv x hx'.1 hx'.2).congr_of_eventuallyEq hfun
    have hiter : (deriv^[2] familyEnergy) x = deriv (deriv familyEnergy) x := by
      have hcomp : (deriv^[2]) familyEnergy = deriv (deriv familyEnergy) := by
        rw [show (2 : ℕ) = Nat.succ 1 from rfl, Function.iterate_succ, Function.iterate_one]
        rfl
      rw [hcomp]
    rw [hiter, h2.deriv]
    exact familyEnergyDeriv2_pos x hx'.1 hx'.2

end ThomsonNine.Family
