import ThomsonNine.SecondDerivative
import ThomsonNine.CandidateMem
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Order.OrderClosed

open ThomsonNine
open ThomsonNine.Family

namespace ThomsonNine.Family

/-! Strict monotonicity of E' and the strict global minimum of the family energy on (0,1). -/

lemma strictMonoOn_familyEnergyDeriv :
    StrictMonoOn familyEnergyDeriv (Set.Ioo (0 : ℝ) 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioo (0 : ℝ) 1)
    continuousOn_familyEnergyDeriv_Ioo ?_
  intro x hx
  have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := by simpa only [interior_Ioo] using hx
  rw [(hasDerivAt_familyEnergyDeriv x hx'.1 hx'.2).deriv]
  exact familyEnergyDeriv2_pos x hx'.1 hx'.2

lemma familyEnergyDeriv_neg_of_lt {r s : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hs : 0 < s) (hs1 : s < 1) (h : s < r) (hz : familyEnergyDeriv r = 0) :
    familyEnergyDeriv s < 0 := by
  have hmono := strictMonoOn_familyEnergyDeriv
    (Set.mem_Ioo.mpr ⟨hs, hs1⟩) (Set.mem_Ioo.mpr ⟨hr, hr1⟩) h
  rwa [hz] at hmono

lemma familyEnergyDeriv_pos_of_gt {r s : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hs : 0 < s) (hs1 : s < 1) (h : r < s) (hz : familyEnergyDeriv r = 0) :
    0 < familyEnergyDeriv s := by
  have hmono := strictMonoOn_familyEnergyDeriv
    (Set.mem_Ioo.mpr ⟨hr, hr1⟩) (Set.mem_Ioo.mpr ⟨hs, hs1⟩) h
  rwa [hz] at hmono

lemma differentiableOn_familyEnergy :
    DifferentiableOn ℝ familyEnergy (Set.Ioo (0 : ℝ) 1) :=
  fun x hx => (hasDerivAt_familyEnergy x hx.1 hx.2).differentiableAt.differentiableWithinAt

theorem familyEnergy_strictAntiOn {r s : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hs : 0 < s) (h : s < r) (hz : familyEnergyDeriv r = 0) :
    familyEnergy r < familyEnergy s := by
  have hmono : StrictAntiOn familyEnergy (Set.Icc s r) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc s r) ?_ ?_
    · exact (differentiableOn_familyEnergy.mono (by
        intro x hx
        exact ⟨lt_of_lt_of_le hs hx.1, lt_of_le_of_lt hx.2 hr1⟩)).continuousOn
    · intro x hx
      have hx' : x ∈ Set.Ioo s r := by simpa only [interior_Icc] using hx
      rw [(hasDerivAt_familyEnergy x (lt_trans hs hx'.1) (lt_trans hx'.2 hr1)).deriv]
      exact familyEnergyDeriv_neg_of_lt hr hr1 (lt_trans hs hx'.1) (lt_trans hx'.2 hr1) hx'.2 hz
  exact hmono (show s ∈ Set.Icc s r from ⟨le_rfl, h.le⟩)
    (show r ∈ Set.Icc s r from ⟨h.le, le_rfl⟩) h

theorem familyEnergy_strictMonoOn {r s : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hs : 0 < s) (hs1 : s < 1) (h : r < s) (hz : familyEnergyDeriv r = 0) :
    familyEnergy r < familyEnergy s := by
  have hmono : StrictMonoOn familyEnergy (Set.Icc r s) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc r s) ?_ ?_
    · exact (differentiableOn_familyEnergy.mono (by
        intro x hx
        exact ⟨lt_of_lt_of_le hr hx.1, lt_of_le_of_lt hx.2 hs1⟩)).continuousOn
    · intro x hx
      have hx' : x ∈ Set.Ioo r s := by simpa only [interior_Icc] using hx
      rw [(hasDerivAt_familyEnergy x (lt_trans hr hx'.1) (lt_trans hx'.2 hs1)).deriv]
      exact familyEnergyDeriv_pos_of_gt hr hr1 (lt_trans hr hx'.1) (lt_trans hx'.2 hs1) hx'.1 hz
  exact hmono (show r ∈ Set.Icc r s from ⟨le_rfl, h.le⟩)
    (show s ∈ Set.Icc r s from ⟨h.le, le_rfl⟩) h

theorem familyEnergy_min (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hz : familyEnergyDeriv r = 0) :
    ∀ s, 0 < s → s < 1 → s ≠ r → familyEnergy r < familyEnergy s := by
  intro s hs hs1 hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact familyEnergy_strictAntiOn hr hr1 hs h hz
  · exact familyEnergy_strictMonoOn hr hr1 hs hs1 h hz

theorem exists_unique_familyEnergy_min :
    ∃! r : ℝ, 0 < r ∧ r < 1 ∧ familyEnergyDeriv r = 0 ∧
      ∀ s, 0 < s → s < 1 → s ≠ r → familyEnergy r < familyEnergy s := by
  rcases exists_unique_stationary_point with ⟨r, ⟨hr, hr1, _hderiv, hzero⟩, huniq⟩
  refine ⟨r, ⟨hr, hr1, hzero, familyEnergy_min r hr hr1 hzero⟩, ?_⟩
  rintro s ⟨hs, hs1, hzs, _hmin⟩
  exact huniq s ⟨hs, hs1, hasDerivAt_familyEnergy s hs hs1, hzs⟩


theorem energy_candidate_min (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hz : familyEnergyDeriv r = 0) :
    ∀ s, 0 < s → s < 1 → s ≠ r → energy (candidate r) < energy (candidate s) := by
  intro s hs hs1 hne
  rw [energy_candidate r hr hr1, energy_candidate s hs hs1]
  exact familyEnergy_min r hr hr1 hz s hs hs1 hne


theorem exists_candidate_with_family_min :
    ∃ r, 0 < r ∧ r < 1 ∧ candidate r ∈ SphereConfig 9 ∧
      HasDerivAt familyEnergy (familyEnergyDeriv r) r ∧ familyEnergyDeriv r = 0 ∧
      ∀ s, 0 < s → s < 1 → s ≠ r → energy (candidate r) < energy (candidate s) := by
  rcases exists_unique_stationary_point with ⟨r, ⟨hr, hr1, hderiv, hzero⟩, _huniq⟩
  exact ⟨r, hr, hr1, candidate_mem_sphere r hr hr1, hderiv, hzero,
    energy_candidate_min r hr hr1 hzero⟩


theorem familyEnergy_strictAntiOn_Ioo (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hz : familyEnergyDeriv r = 0) :
    StrictAntiOn familyEnergy (Set.Ioo (0 : ℝ) r) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioo (0 : ℝ) r) ?_ ?_
  · exact (differentiableOn_familyEnergy.mono (by
      intro x hx
      exact ⟨hx.1, lt_trans hx.2 hr1⟩)).continuousOn
  · intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) r := by simpa only [interior_Ioo] using hx
    rw [(hasDerivAt_familyEnergy x hx'.1 (lt_trans hx'.2 hr1)).deriv]
    exact familyEnergyDeriv_neg_of_lt hr hr1 hx'.1 (lt_trans hx'.2 hr1) hx'.2 hz

theorem familyEnergy_strictMonoOn_Ioo (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hz : familyEnergyDeriv r = 0) :
    StrictMonoOn familyEnergy (Set.Ioo (r : ℝ) 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioo r 1) ?_ ?_
  · exact (differentiableOn_familyEnergy.mono (by
      intro x hx
      exact ⟨lt_trans hr hx.1, hx.2⟩)).continuousOn
  · intro x hx
    have hx' : x ∈ Set.Ioo (r : ℝ) 1 := by simpa only [interior_Ioo] using hx
    rw [(hasDerivAt_familyEnergy x (lt_trans hr hx'.1) hx'.2).deriv]
    exact familyEnergyDeriv_pos_of_gt hr hr1 (lt_trans hr hx'.1) hx'.2 hx'.1 hz

end ThomsonNine.Family
