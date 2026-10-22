import Contact.MissingValue
import Moment.Complete

noncomputable section
namespace ThomsonNine.ActualContact
open scoped BigOperators

theorem CFG_equation : (∑ h : Fin 190, M 30 h*ActualR.X h)=rhs 30 :=
  CFG_equation_of_weighted_zero (CandidateMoment.constructed_weightedF_zero ActualR.X)
theorem CFG_residual_zero : ActualR.residual (point 30)=0 :=
  residual_zero_of_value_equation 30 rfl CFG_equation

theorem all_value_equations (j : Fin 12) :
    (∑ h : Fin 190, M (valueRows j) h*ActualR.X h)=rhs (valueRows j) := by
  by_cases hj : j=8
  · subst j
    exact CFG_equation
  · exact selected_value j hj

theorem all_value_kinds (j : Fin 12) : (rows (valueRows j)).kind=0 := by
  fin_cases j <;> rfl

theorem all_actual_contact_values (j : Fin 12) : ActualR.residual (point (valueRows j))=0 :=
  residual_zero_of_value_equation _ (all_value_kinds j) (all_value_equations j)
end ThomsonNine.ActualContact
