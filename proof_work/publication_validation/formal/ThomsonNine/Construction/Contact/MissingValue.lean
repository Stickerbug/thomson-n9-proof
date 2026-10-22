import ThomsonNine.Construction.Contact.Weights
import ThomsonNine.Construction.Contact.SystemCertificate

-- Isolated source: Contact.MissingValue
noncomputable section
namespace ThomsonNine.ActualContact
open ThomsonNine.ContactJet
open scoped BigOperators
theorem weighted_errors (X : Fin 190 → ℝ) :
    (∑ j : Fin 12, (triangleWeights j : ℝ)*((∑ h : Fin 190, M (valueRows j) h*X h)-rhs (valueRows j)))=
      7*CandidateMoment.weightedF X RefinedRadius.radius := by
  simp only [mul_sub,Finset.sum_sub_distrib,weighted_value_M,weighted_rhs,sub_zero]

theorem selected_value (j : Fin 12) (hj : j≠8) :
    (∑ h : Fin 190, M (valueRows j) h*ActualR.X h)=rhs (valueRows j) := by
  fin_cases j
  · exact SystemCertificate.selected_equations 30
  · exact SystemCertificate.selected_equations 27
  · exact SystemCertificate.selected_equations 31
  · exact SystemCertificate.selected_equations 32
  · exact SystemCertificate.selected_equations 26
  · exact SystemCertificate.selected_equations 21
  · exact SystemCertificate.selected_equations 25
  · exact SystemCertificate.selected_equations 24
  · exact False.elim (hj rfl)
  · exact SystemCertificate.selected_equations 22
  · exact SystemCertificate.selected_equations 29
  · exact SystemCertificate.selected_equations 28
theorem CFG_equation_of_weighted_zero
    (hf : CandidateMoment.weightedF ActualR.X RefinedRadius.radius=0) :
    (∑ h : Fin 190, M 30 h*ActualR.X h)=rhs 30 := by
  have hsingle : (∑ j : Fin 12, (triangleWeights j : ℝ)*
      ((∑ h : Fin 190, M (valueRows j) h*ActualR.X h)-rhs (valueRows j)))=
      (triangleWeights 8 : ℝ)*((∑ h : Fin 190, M (valueRows 8) h*ActualR.X h)-rhs (valueRows 8)) := by
    apply Finset.sum_eq_single 8
    · intro j hj hne
      rw [selected_value j hne,sub_self,mul_zero]
    · simp
  have hw := weighted_errors ActualR.X
  rw [hsingle,hf] at hw
  norm_num [triangleWeights,valueRows] at hw
  linarith

theorem residual_at_value_row (row : Fin 45) (hk : (rows row).kind=0) :
    ActualR.residual (point row)=rhs row-polynomialContact ActualR.X (point row) := by
  simp only [ActualR.residual,polynomialContact,ActualF.Constants.c,ActualF.Constants.F111,
    point,ActualHermite.H_eval,rhs,hk,ite_true,Fin.sum_univ_three]
  ring

theorem residual_zero_of_value_equation (row : Fin 45) (hk : (rows row).kind=0)
    (he : (∑ h : Fin 190, M row h*ActualR.X h)=rhs row) : ActualR.residual (point row)=0 := by
  rw [residual_at_value_row row hk]
  have hp : polynomialContact ActualR.X (point row)=rhs row := by
    rw [← valueRow_sum]
    simp only [M,hk,ite_true] at he
    simpa only [mul_comm] using he
  rw [hp,sub_self]

theorem CFG_residual_zero_of_weighted_zero
    (hf : CandidateMoment.weightedF ActualR.X RefinedRadius.radius=0) : ActualR.residual (point 30)=0 :=
  residual_zero_of_value_equation 30 rfl (CFG_equation_of_weighted_zero hf)
end ThomsonNine.ActualContact
