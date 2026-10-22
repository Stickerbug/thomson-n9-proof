import F.Expansion
noncomputable section
namespace ThomsonNine.ActualF
open ThomsonNine.ThreePoint
open scoped BigOperators

theorem swap12 (X : Fin 190 → ℝ) (u v t : ℝ) : F X u v t=F X v u t := by
  rw [F_eq_matrix_pairing,F_eq_matrix_pairing]
  simp only [S3_swap12 _ _ u v t]
theorem swap23 (X : Fin 190 → ℝ) (u v t : ℝ) : F X u v t=F X u t v := by
  rw [F_eq_matrix_pairing,F_eq_matrix_pairing]
  simp only [S3_swap23 _ _ u v t]
end ThomsonNine.ActualF
