import ThomsonNine.IntervalSparseDerivative
import Mathlib.Analysis.Calculus.Deriv.Pow

-- Isolated source: Algebra.SparseCurve
noncomputable section
namespace ThomsonNine.Interval.SparsePolynomial
open scoped BigOperators

theorem monomial_curve_derivative (e : Exp3) (c : ℝ) (curve : ℝ → (Fin 3 → ℝ))
    (velocity : Fin 3 → ℝ) (s : ℝ) (hd : ∀ i, HasDerivAt (fun t => curve t i) (velocity i) s) :
    HasDerivAt (fun t => c*monomial e (curve t))
      (∑ i : Fin 3, derivativeCoeff i e c*monomial (lowerExponent i e) (curve s)*velocity i) s := by
  have h := ((((hd 0).pow (e 0)).mul ((hd 1).pow (e 1))).mul ((hd 2).pow (e 2))).const_mul c
  convert h using 1
  · rfl
  · simp [derivativeCoeff_eq_mul,monomial,lowerExponent,Fin.sum_univ_three]
    ring

def directionalDerivative {α : Type*} (e : α → Exp3) (c : α → ℝ)
    (x velocity : Fin 3 → ℝ) (l : List α) : ℝ :=
  ∑ i : Fin 3, formalDerivative e c i x l*velocity i

theorem eval_curve_derivative {α : Type*} (e : α → Exp3) (c : α → ℝ) (l : List α)
    (curve : ℝ → (Fin 3 → ℝ)) (velocity : Fin 3 → ℝ) (s : ℝ)
    (hd : ∀ i, HasDerivAt (fun t => curve t i) (velocity i) s) :
    HasDerivAt (fun t => eval e c (curve t) l) (directionalDerivative e c (curve s) velocity l) s := by
  induction l with
  | nil => simpa [eval,directionalDerivative,formalDerivative] using hasDerivAt_const s (0 : ℝ)
  | cons a l ih =>
    have h := (monomial_curve_derivative (e a) (c a) curve velocity s hd).add ih
    convert h using 1
    · rfl
    · simp only [directionalDerivative,formalDerivative,eval,add_mul,Finset.sum_add_distrib]

def directionalHessian {α : Type*} (e : α → Exp3) (c : α → ℝ)
    (x velocity : Fin 3 → ℝ) (l : List α) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, formalHessianEntry e c i j x l*velocity j*velocity i

theorem directionalDerivative_curve {α : Type*} (e : α → Exp3) (c : α → ℝ) (l : List α)
    (curve : ℝ → (Fin 3 → ℝ)) (velocity : Fin 3 → ℝ) (s : ℝ)
    (hd : ∀ i, HasDerivAt (fun t => curve t i) (velocity i) s) :
    HasDerivAt (fun t => directionalDerivative e c (curve t) velocity l)
      (directionalHessian e c (curve s) velocity l) s := by
  have h (i : Fin 3) :=
    (eval_curve_derivative (fun k => lowerExponent i (e k)) (fun k => derivativeCoeff i (e k) (c k))
      l curve velocity s hd).mul_const (velocity i)
  have hsum := HasDerivAt.fun_sum (u:=Finset.univ) (fun i _ => h i)
  convert hsum using 1
  · rfl
  · simp only [directionalHessian,directionalDerivative,formalHessianEntry,Finset.sum_mul]
end ThomsonNine.Interval.SparsePolynomial
