import ThomsonNine.ActualHermite

-- Isolated source: Hermite.Energy
noncomputable section
namespace ThomsonNine.ActualHermite
open ThomsonNine.RefinedRadius

theorem value_A : value 9 = (Real.sqrt 3*radius)⁻¹ := by
  have h : 2-2*node 9=3*radius^2 := by simp [node]; ring
  rw [value,h,Real.sqrt_mul (by norm_num),Real.sqrt_sq (le_of_lt radius_pos)]
theorem value_B : value 7 = (2*Real.sqrt (1-radius^2))⁻¹ := by
  have h : 2-2*node 7=4*(1-radius^2) := by simp [node]; ring
  have hs : Real.sqrt (4 : ℝ)=2 := by
    rw [show (4 : ℝ)=2^2 by norm_num,Real.sqrt_sq (by norm_num)]
  rw [value,h,Real.sqrt_mul (by norm_num),hs]
theorem value_C : value 2 = (Real.sqrt (4-radius^2))⁻¹ := by
  have h : 2-2*node 2=4-radius^2 := by simp [node]; ring
  rw [value,h]
theorem value_D : value 4 = (Real.sqrt 3)⁻¹ := by norm_num [value,node]
theorem value_F : value 10 = (Real.sqrt (2-radius))⁻¹ := by
  have h : 2-2*node 10=2-radius := by simp [node]; ring
  rw [value,h]
theorem value_G : value 3 = (Real.sqrt (2+2*radius))⁻¹ := by
  simp [value,node]
theorem contact_energy_identity :
    6*value 9+3*value 7+6*value 2+3*value 4+12*value 10+6*value 3 = familyEnergy radius := by
  rw [value_A,value_B,value_C,value_D,value_F,value_G,Family.familyEnergy_alt radius_pos radius_lt_one]
  simp only [div_eq_mul_inv]
  ring
end ThomsonNine.ActualHermite
