import ThomsonNine.SecondDerivative
import ThomsonNine.CandidateMem

/-!
# Assembly of the frozen claim from a single analytic input

`Statement.ThomsonNineClaim` bundles the candidate geometry, the stationary point,
the energy identity and the global lower bound.  Everything except the global lower
bound is proved in `Stationary`, `SecondDerivative`, `CandidateMem` and `Family`.
This file makes that decomposition machine checked: the frozen claim is *equivalent*
to the existence of a stationary point whose family energy bounds the energy of every
configuration on the sphere.  The remaining unformalized bridge is exactly the
global lower bound (the coverage/certificate input).
-/

open scoped BigOperators

namespace ThomsonNine

open ThomsonNine.Family

/-- The frozen claim is equivalent to the existence of a stationary point whose
family energy is a global lower bound. -/
theorem thomsonNineClaim_iff_global_lower_bound :
    ThomsonNineClaim ↔
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧ HasDerivAt familyEnergy 0 r ∧
        ∀ x ∈ SphereConfig 9, familyEnergy r ≤ energy x := by
  constructor
  · rintro ⟨r, hr, hr1, hder, -, -, -, hlow⟩
    exact ⟨r, hr, hr1, hder, hlow⟩
  · rintro ⟨r, hr, hr1, hder, hlow⟩
    have hzr : familyEnergyDeriv r = 0 :=
      (hasDerivAt_familyEnergy r hr hr1).unique hder
    refine ⟨r, hr, hr1, hder, ?_, candidate_mem_sphere r hr hr1,
      energy_candidate r hr hr1, hlow⟩
    intro s hs hs1 hders
    have hzs : familyEnergyDeriv s = 0 :=
      (hasDerivAt_familyEnergy s hs hs1).unique hders
    exact (stationary_point_unique r s hr hr1 hs hs1 hzr hzs).symm

/-- Pointwise form of the reduction, convenient for plugging in a certificate. -/
theorem thomsonNineClaim_of_pointwise
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (hder : HasDerivAt familyEnergy 0 r)
    (hlow : ∀ x ∈ SphereConfig 9, familyEnergy r ≤ energy x) :
    ThomsonNineClaim :=
  thomsonNineClaim_iff_global_lower_bound.mpr ⟨r, hr, hr1, hder, hlow⟩

end ThomsonNine
