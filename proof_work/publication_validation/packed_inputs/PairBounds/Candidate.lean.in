import PairBounds.Inputs
import Matrices.Actual

noncomputable section
namespace ThomsonNine.PairBounds
open ThomsonNine.ActualHermite.CoefficientData
theorem candidate_upper_input : (ActualContact.inputE.hi : ℚ)<(unitScale : ℚ)*U := by decide +kernel
theorem candidate_energy_lt_U : familyEnergy RefinedRadius.radius<(U : ℝ) := by
  have h := ActualContact.E_mem
  have hu : (ActualContact.inputE.hi : ℝ)<(unitScale : ℝ)*(U : ℝ) := by exact_mod_cast candidate_upper_input
  have hs : (0 : ℝ)<unitScale := by exact_mod_cast unitScale_pos
  rw [CertificateMatrices.contact_energy_eq_family] at h
  have hlt := h.2.trans_lt hu
  by_contra hn
  have hp := mul_nonneg (le_of_lt hs) (sub_nonneg.mpr (le_of_not_gt hn))
  nlinarith
end ThomsonNine.PairBounds
