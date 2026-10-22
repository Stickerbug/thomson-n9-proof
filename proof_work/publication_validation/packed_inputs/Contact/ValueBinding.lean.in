import Contact.FJet
import R.Residual

noncomputable section
namespace ThomsonNine.ActualContact
open ThomsonNine.ContactJet
open scoped BigOperators

def polynomialContact (X : Fin 190 → ℝ) (x : Point) : ℝ :=
  7*ActualF.F X (x 0) (x 1) (x 2)+
    (∑ j : Fin 3, ActualF.F X 1 (x j) (x j))+(1/8)*ActualF.F X 1 1 1

theorem valueRow_sum (X : Fin 190 → ℝ) (row : Fin 45) :
    (∑ h : Fin 190, X h*valueRow row h)=polynomialContact X (point row) := by
  have hf (x : Point) : (∑ h : Fin 190, X h*(jet x h).value)=ActualF.F X (x 0) (x 1) (x 2) := by
    rw [← FJet_value]
    exact (FJet_along X x).1
  simp only [valueRow,mul_add,Finset.mul_sum,Finset.sum_add_distrib]
  have h7 : (∑ h : Fin 190, X h*(7*(jet (point row) h).value))=7*ActualF.F X (point row 0) (point row 1) (point row 2) := by
    rw [← hf (point row),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    ring
  have hd : (∑ h : Fin 190, ∑ j : Fin 3, X h*(jet (diagonal ((rows row).nodes j)) h).value)=
      ∑ j : Fin 3, ActualF.F X 1 (point row j) (point row j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hf]
    rfl
  have hc : (∑ h : Fin 190, X h*((1/8)*(jet ones h).value))=(1/8)*ActualF.F X 1 1 1 := by
    have ho : (∑ h : Fin 190, X h*(jet ones h).value)=ActualF.F X 1 1 1 := hf ones
    rw [← ho,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    ring
  rw [h7,hd,hc]
  rfl

theorem gradientRow_sum (X : Fin 190 → ℝ) (row : Fin 45) (j : Fin 3) :
    (∑ h : Fin 190, X h*gradientRow row h j)=
      7*(FJet X (point row)).gradient j+
      (FJet X (diagonal ((rows row).nodes j))).gradient 1+
      (FJet X (diagonal ((rows row).nodes j))).gradient 2 := by
  simp only [gradientRow,mul_add,Finset.sum_add_distrib,FJet_gradient,Finset.mul_sum]
  congr 2
  apply Finset.sum_congr rfl
  intro h hh
  ring
end ThomsonNine.ActualContact
