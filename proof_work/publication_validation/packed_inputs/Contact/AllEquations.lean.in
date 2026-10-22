import Contact.RedundantRows
import Contact.GradientCompatibility
import Contact.CompletedValues
noncomputable section
namespace ThomsonNine.ActualContact
open scoped BigOperators

theorem equations_except_ABC (row : Fin 45) (hr : row≠6) :
    (∑ h : Fin 190, M row h*ActualR.X h)=rhs row := by
  fin_cases row
  · exact SystemCertificate.selected_equations 30
  · exact (matrix_redundant_01 ActualR.X).trans ((SystemCertificate.selected_equations 16).trans rhs_redundant_01.symm)
  · exact SystemCertificate.selected_equations 16
  · exact (matrix_redundant_03 ActualR.X).trans ((SystemCertificate.selected_equations 16).trans rhs_redundant_03.symm)
  · exact SystemCertificate.selected_equations 27
  · exact SystemCertificate.selected_equations 7
  · exact False.elim (hr rfl)
  · exact SystemCertificate.selected_equations 0
  · exact SystemCertificate.selected_equations 31
  · exact SystemCertificate.selected_equations 19
  · exact SystemCertificate.selected_equations 1
  · exact (matrix_redundant_11 ActualR.X).trans ((SystemCertificate.selected_equations 1).trans rhs_redundant_11.symm)
  · exact SystemCertificate.selected_equations 32
  · exact SystemCertificate.selected_equations 15
  · exact SystemCertificate.selected_equations 9
  · exact (matrix_redundant_15 ActualR.X).trans ((SystemCertificate.selected_equations 9).trans rhs_redundant_15.symm)
  · exact SystemCertificate.selected_equations 26
  · exact SystemCertificate.selected_equations 18
  · exact SystemCertificate.selected_equations 20
  · exact SystemCertificate.selected_equations 2
  · exact SystemCertificate.selected_equations 21
  · exact SystemCertificate.selected_equations 4
  · exact SystemCertificate.selected_equations 17
  · exact (matrix_redundant_23 ActualR.X).trans ((SystemCertificate.selected_equations 17).trans rhs_redundant_23.symm)
  · exact SystemCertificate.selected_equations 25
  · exact SystemCertificate.selected_equations 6
  · exact (matrix_redundant_26 ActualR.X).trans ((SystemCertificate.selected_equations 6).trans rhs_redundant_26.symm)
  · exact SystemCertificate.selected_equations 24
  · exact SystemCertificate.selected_equations 3
  · exact (matrix_redundant_29 ActualR.X).trans ((SystemCertificate.selected_equations 3).trans rhs_redundant_29.symm)
  · exact CFG_equation
  · exact SystemCertificate.selected_equations 14
  · exact SystemCertificate.selected_equations 13
  · exact SystemCertificate.selected_equations 23
  · exact SystemCertificate.selected_equations 22
  · exact (matrix_zero_35 ActualR.X).trans rhs_zero_35.symm
  · exact (matrix_zero_36 ActualR.X).trans rhs_zero_36.symm
  · exact SystemCertificate.selected_equations 29
  · exact SystemCertificate.selected_equations 8
  · exact SystemCertificate.selected_equations 10
  · exact (matrix_redundant_40 ActualR.X).trans ((SystemCertificate.selected_equations 10).trans rhs_redundant_40.symm)
  · exact SystemCertificate.selected_equations 28
  · exact SystemCertificate.selected_equations 12
  · exact SystemCertificate.selected_equations 5
  · exact SystemCertificate.selected_equations 11

theorem ABC_equation : (∑ h : Fin 190, M 6 h*ActualR.X h)=rhs 6 := by
  have hw : (∑ row : Fin 45, leftGradientWeight row*((∑ h : Fin 190, M row h*ActualR.X h)-rhs row))=0 := by
    simp only [mul_sub,Finset.sum_sub_distrib,leftGradient_matrix_zero,leftGradient_rhs_zero,sub_self]
  have hsingle : (∑ row : Fin 45, leftGradientWeight row*((∑ h : Fin 190, M row h*ActualR.X h)-rhs row))=
      leftGradientWeight 6*((∑ h : Fin 190, M 6 h*ActualR.X h)-rhs 6) := by
    apply Finset.sum_eq_single 6
    · intro row hrow hne
      rw [equations_except_ABC row hne,sub_self,mul_zero]
    · simp
  rw [hsingle] at hw
  have hp : 0<leftGradientWeight 6 := by
    change 0<48*RefinedRadius.radius
    exact mul_pos (by norm_num) RefinedRadius.radius_pos
  exact sub_eq_zero.mp ((mul_eq_zero.mp hw).resolve_left (ne_of_gt hp))

theorem all_45_equations (row : Fin 45) : (∑ h : Fin 190, M row h*ActualR.X h)=rhs row := by
  by_cases hr : row=6
  · subst row
    exact ABC_equation
  · exact equations_except_ABC row hr
end ThomsonNine.ActualContact
