import Contact.WeightedDerivative
noncomputable section
namespace ThomsonNine.ActualContact
open scoped BigOperators

theorem row_sum (X : Fin 190 → ℝ) (row : Fin 45) :
    (∑ h : Fin 190, M row h*X h)=
      if (rows row).kind=0 then polynomialContact X (point row)
      else if (rows row).kind=1 then contactGradient X (point row) (rows row).axis
      else gramGradient (point row) 0*contactGradient X (point row) (rows row).axis-
        gramGradient (point row) (rows row).axis*contactGradient X (point row) 0 := by
  simp only [M]
  split_ifs with h0 h1
  · simpa only [mul_comm] using valueRow_sum X row
  · simpa only [mul_comm] using (contactGradient_row X row _).symm
  · simp only [sub_mul,Finset.sum_sub_distrib]
    rw [contactGradient_row,contactGradient_row]
    simp only [Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro h hh <;> ring
end ThomsonNine.ActualContact
