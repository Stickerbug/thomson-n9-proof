import Contact.AllEquations
import Mathlib.Analysis.Calculus.Deriv.Polynomial

set_option maxRecDepth 100000
noncomputable section
namespace ThomsonNine.ActualContact
open ThomsonNine.ContactJet ThomsonNine.ActualHermite Polynomial
open scoped BigOperators
attribute [local irreducible] FJet contactGradient

def residualGradient (x : Point) (j : Fin 3) : ℝ := H.derivative.eval (x j)-contactGradient ActualR.X x j

theorem residual_eq_contact (x : Point) : ActualR.residual x=
    (∑ j : Fin 3, H.eval (x j))-polynomialContact ActualR.X x-(1/12)*E := by
  simp only [ActualR.residual,polynomialContact,ActualF.Constants.c,ActualF.Constants.F111,Fin.sum_univ_three]
  ring

theorem residual_curve_derivative (x : Point) (curve : ℝ → Point) (velocity : Point) (s : ℝ)
    (hc : curve s=x) (hd : ∀ j, HasDerivAt (fun t => curve t j) (velocity j) s) :
    HasDerivAt (fun t => ActualR.residual (curve t)) (∑ j : Fin 3, residualGradient x j*velocity j) s := by
  have hH (j : Fin 3) : HasDerivAt (fun t => H.eval (curve t j)) (H.derivative.eval (x j)*velocity j) s := by
    have h := (H.hasDerivAt (curve s j)).comp s (hd j)
    rw [hc] at h
    exact h
  have hsum := HasDerivAt.fun_sum (u:=Finset.univ) (fun j _ => hH j)
  have hP := polynomialContact_derivative ActualR.X x curve velocity s hc hd
  have h := (hsum.sub hP).sub (hasDerivAt_const s ((1/12)*E))
  have he : (∑ j : Fin 3, residualGradient x j*velocity j)=
      (∑ j : Fin 3, H.derivative.eval (x j)*velocity j)-
      (∑ j : Fin 3, contactGradient ActualR.X x j*velocity j)-0 := by
    simp only [residualGradient,sub_mul,Finset.sum_sub_distrib,sub_zero]
  rw [he]
  convert h using 1
  funext t
  exact residual_eq_contact (curve t)

theorem H_derivative_point (row : Fin 45) (j : Fin 3) : H.derivative.eval (point row j)=(value ((rows row).nodes j))^3 := by
  rw [point,H_derivative_eval,H_eval]

theorem actual_interior_gradient_zero (row : Fin 45) (hk : (rows row).kind=1) :
    residualGradient (point row) (rows row).axis=0 := by
  have he := all_45_equations row
  rw [row_sum] at he
  simp only [rhs,hk] at he
  norm_num at he
  simp only [residualGradient,H_derivative_point]
  linarith

theorem actual_boundary_tangent_zero (row : Fin 45) (hk : (rows row).kind=2) :
    gramGradient (point row) 0*residualGradient (point row) (rows row).axis-
      gramGradient (point row) (rows row).axis*residualGradient (point row) 0=0 := by
  have he := all_45_equations row
  rw [row_sum] at he
  simp only [rhs,hk] at he
  norm_num at he
  simp only [residualGradient,H_derivative_point]
  linear_combination -he
end ThomsonNine.ActualContact
