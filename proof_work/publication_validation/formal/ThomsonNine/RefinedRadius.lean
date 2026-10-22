import ThomsonNine.RadiusEndpointLo
import ThomsonNine.RadiusEndpointHi

noncomputable section
namespace ThomsonNine.RefinedRadius
open ThomsonNine.Interval ThomsonNine.Interval.RatInterval ThomsonNine.Family

def enclosure : RatInterval := ⟨RadiusLo.point,RadiusHi.point, by decide +kernel⟩

theorem rational_bounds : 0 < RadiusLo.point ∧ RadiusLo.point < RadiusHi.point ∧ RadiusHi.point < 1 := by
  decide +kernel

theorem exists_root : ∃ r : ℝ, enclosure.mem r ∧ familyEnergyDeriv r = 0 := by
  have hlo : (0 : ℝ) < RadiusLo.point := by exact_mod_cast rational_bounds.1
  have hhi : (RadiusHi.point : ℝ) < 1 := by exact_mod_cast rational_bounds.2.2
  have hle : (RadiusLo.point : ℝ) ≤ RadiusHi.point := by exact_mod_cast le_of_lt rational_bounds.2.1
  have hsub : Set.Icc (RadiusLo.point : ℝ) RadiusHi.point ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro x hx
    exact ⟨lt_of_lt_of_le hlo hx.1, lt_of_le_of_lt hx.2 hhi⟩
  have hc := continuousOn_familyEnergyDeriv_Ioo.mono hsub
  have hi := intermediate_value_Icc hle hc
  obtain ⟨r,hr,hzero⟩ := hi (show (0 : ℝ) ∈ Set.Icc
    (familyEnergyDeriv RadiusLo.point) (familyEnergyDeriv RadiusHi.point) from
      ⟨le_of_lt RadiusLo.derivative_neg,le_of_lt RadiusHi.derivative_pos⟩)
  exact ⟨r,hr,hzero⟩

/-- The actual stationary radius, chosen from the proved narrow real bracket. -/
def radius : ℝ := Classical.choose exists_root

theorem radius_mem : enclosure.mem radius := (Classical.choose_spec exists_root).1
theorem radius_derivative_zero : familyEnergyDeriv radius = 0 := (Classical.choose_spec exists_root).2

theorem radius_pos : 0 < radius := by
  have hlo : (0 : ℝ) < RadiusLo.point := by exact_mod_cast rational_bounds.1
  exact hlo.trans_le radius_mem.1

theorem radius_lt_one : radius < 1 := by
  have hhi : (RadiusHi.point : ℝ) < 1 := by exact_mod_cast rational_bounds.2.2
  exact radius_mem.2.trans_lt hhi

theorem radius_stationary : HasDerivAt familyEnergy 0 radius := by
  simpa only [radius_derivative_zero] using hasDerivAt_familyEnergy radius radius_pos radius_lt_one

theorem radius_unique (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hzero : familyEnergyDeriv r = 0) : r = radius :=
  stationary_point_unique r radius hr hr1 radius_pos radius_lt_one hzero radius_derivative_zero
end ThomsonNine.RefinedRadius
