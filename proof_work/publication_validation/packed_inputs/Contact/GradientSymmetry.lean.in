import Contact.CurveDerivative
import F.Symmetry

set_option maxRecDepth 100000
noncomputable section
namespace ThomsonNine.ActualContact
open ThomsonNine.ContactJet
open scoped BigOperators
attribute [local irreducible] FJet contactGradient

theorem polynomialContact_swap12 (X : Fin 190 → ℝ) (u v t : ℝ) :
    polynomialContact X ![u,v,t]=polynomialContact X ![v,u,t] := by
  simp only [polynomialContact,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  rw [ActualF.swap12 X u v t]
  ring

theorem polynomialContact_swap23 (X : Fin 190 → ℝ) (u v t : ℝ) :
    polynomialContact X ![u,v,t]=polynomialContact X ![u,t,v] := by
  simp only [polynomialContact,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  rw [ActualF.swap23 X u v t]
  ring

theorem polynomialContact_partial (X : Fin 190 → ℝ) (x : Point) (i : Fin 3) :
    HasDerivAt (fun t => polynomialContact X (Function.update x i t)) (contactGradient X x i) (x i) := by
  have hd (j : Fin 3) : HasDerivAt (fun t => Function.update x i t j)
      (if j=i then 1 else 0) (x i) := by
    by_cases h : j=i
    · subst j
      convert hasDerivAt_id' (x i) using 1 <;> simp
    · simpa only [Function.update_of_ne h,if_neg h] using hasDerivAt_const (x i) (x j)
  have h := polynomialContact_derivative X x (fun t => Function.update x i t)
    (fun j => if j=i then 1 else 0) (x i) (Function.update_eq_self _ _) hd
  convert h using 1
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem contactGradient_repeat12 (X : Fin 190 → ℝ) (a b : ℝ) :
    contactGradient X ![a,a,b] 0=contactGradient X ![a,a,b] 1 := by
  have h0 := polynomialContact_partial X ![a,a,b] 0
  have h1 := polynomialContact_partial X ![a,a,b] 1
  have he : (fun t => polynomialContact X (Function.update (![a,a,b] : Point) 0 t))=
      (fun t => polynomialContact X (Function.update (![a,a,b] : Point) 1 t)) := by
    funext t
    have e0 : Function.update (![a,a,b] : Point) 0 t=![t,a,b] := by
      funext i;fin_cases i <;> simp
    have e1 : Function.update (![a,a,b] : Point) 1 t=![a,t,b] := by
      funext i;fin_cases i <;> simp
    rw [e0,e1]
    exact polynomialContact_swap12 X t a b
  rw [he] at h0
  exact h0.unique h1

theorem contactGradient_repeat23 (X : Fin 190 → ℝ) (a b : ℝ) :
    contactGradient X ![a,b,b] 1=contactGradient X ![a,b,b] 2 := by
  have h1 := polynomialContact_partial X ![a,b,b] 1
  have h2 := polynomialContact_partial X ![a,b,b] 2
  have he : (fun t => polynomialContact X (Function.update (![a,b,b] : Point) 1 t))=
      (fun t => polynomialContact X (Function.update (![a,b,b] : Point) 2 t)) := by
    funext t
    have e1 : Function.update (![a,b,b] : Point) 1 t=![a,t,b] := by
      funext i;fin_cases i <;> simp
    have e2 : Function.update (![a,b,b] : Point) 2 t=![a,b,t] := by
      funext i;fin_cases i <;> simp
    rw [e1,e2]
    exact polynomialContact_swap23 X a t b
  rw [he] at h1
  exact h1.unique h2
end ThomsonNine.ActualContact
