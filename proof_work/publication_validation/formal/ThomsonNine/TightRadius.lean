import ThomsonNine.RefinedRadius
import ThomsonNine.RadiusEndpointTightLo
import ThomsonNine.RadiusEndpointTightHi

noncomputable section
namespace ThomsonNine.RefinedRadius
open ThomsonNine.Interval ThomsonNine.Interval.RatInterval ThomsonNine.Family

def tightEnclosure : RatInterval := ⟨RadiusTightLo.point,RadiusTightHi.point,by decide +kernel⟩
theorem tight_rational_bounds : 0 < RadiusTightLo.point ∧ RadiusTightLo.point < RadiusTightHi.point ∧ RadiusTightHi.point < 1 := by
  decide +kernel

theorem tight_width : tightEnclosure.hi-tightEnclosure.lo = 1/(2^800 : ℚ) := by decide +kernel

theorem exists_tight_root : ∃ r : ℝ, tightEnclosure.mem r ∧ familyEnergyDeriv r = 0 := by
  have hlo : (0 : ℝ) < RadiusTightLo.point := by exact_mod_cast tight_rational_bounds.1
  have hhi : (RadiusTightHi.point : ℝ) < 1 := by exact_mod_cast tight_rational_bounds.2.2
  have hle : (RadiusTightLo.point : ℝ) ≤ RadiusTightHi.point := by exact_mod_cast le_of_lt tight_rational_bounds.2.1
  have hsub : Set.Icc (RadiusTightLo.point : ℝ) RadiusTightHi.point ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro x hx
    exact ⟨hlo.trans_le hx.1,hx.2.trans_lt hhi⟩
  obtain ⟨r,hr,hzero⟩ := intermediate_value_Icc hle
    (continuousOn_familyEnergyDeriv_Ioo.mono hsub)
    (show (0 : ℝ) ∈ Set.Icc (familyEnergyDeriv RadiusTightLo.point)
      (familyEnergyDeriv RadiusTightHi.point) from
      ⟨le_of_lt RadiusTightLo.derivative_neg,le_of_lt RadiusTightHi.derivative_pos⟩)
  exact ⟨r,hr,hzero⟩

theorem radius_mem_tight : tightEnclosure.mem radius := by
  obtain ⟨r,hr,hzero⟩ := exists_tight_root
  have hlo : (0 : ℝ) < RadiusTightLo.point := by exact_mod_cast tight_rational_bounds.1
  have hhi : (RadiusTightHi.point : ℝ) < 1 := by exact_mod_cast tight_rational_bounds.2.2
  have heq := radius_unique r (hlo.trans_le hr.1) (hr.2.trans_lt hhi) hzero
  simpa [heq] using hr
end ThomsonNine.RefinedRadius
