import ThomsonNine.IntervalSparsePolynomial
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! Coordinate derivatives of the fixed real sparse polynomial evaluator.

These theorems connect the guarded formal derivative expressions to genuine
`HasDerivAt` and `deriv` along coordinate-update lines. They hold for every real
coefficient family, with no interval or nonzero-coordinate hypotheses. Interval
corollaries retain the explicit coefficient and signed-power memberships.
-/

noncomputable section

namespace ThomsonNine.Interval.SparsePolynomial

open ThomsonNine.Interval.RatInterval

/-- The zero guard agrees with the usual real coefficient rule, including degree zero. -/
theorem derivativeCoeff_eq_mul (axis : Fin 3) (e : Exp3) (a : ℝ) :
    derivativeCoeff axis e a = a * (e axis : ℝ) := by
  by_cases hz : e axis = 0 <;> simp [derivativeCoeff, hz]

/-- Analytic coordinate derivative of one coefficient times a monomial.
Natural subtraction is harmless at exponent zero because the coefficient vanishes. -/
theorem hasDerivAt_monomial_axis (e : Exp3) (a : ℝ)
    (axis : Fin 3) (x : Fin 3 → ℝ) :
    HasDerivAt (fun t : ℝ => a * monomial e (Function.update x axis t))
      (derivativeCoeff axis e a * monomial (lowerExponent axis e) x)
      (x axis) := by
  fin_cases axis
  · convert ((((hasDerivAt_pow (e 0) (x 0)).mul_const
        (x 1 ^ e 1)).mul_const (x 2 ^ e 2)).const_mul a) using 1 <;>
      simp [monomial, lowerExponent, derivativeCoeff_eq_mul,
        Function.update_apply] <;> ring
  · convert ((((hasDerivAt_pow (e 1) (x 1)).const_mul
        (x 0 ^ e 0)).mul_const (x 2 ^ e 2)).const_mul a) using 1 <;>
      simp [monomial, lowerExponent, derivativeCoeff_eq_mul,
        Function.update_apply] <;> ring
  · convert (((hasDerivAt_pow (e 2) (x 2)).const_mul
        (x 0 ^ e 0 * x 1 ^ e 1)).const_mul a) using 1 <;>
      simp [monomial, lowerExponent, derivativeCoeff_eq_mul,
        Function.update_apply] <;> ring

/-- The analytic first coordinate derivative equals the guarded formal evaluator. -/
theorem hasDerivAt_eval_axis {ι : Type*} (e : ι → Exp3) (c : ι → ℝ)
    (axis : Fin 3) (x : Fin 3 → ℝ) (s : List ι) :
    HasDerivAt (fun t : ℝ => eval e c (Function.update x axis t) s)
      (formalDerivative e c axis x s) (x axis) := by
  induction s with
  | nil =>
      simpa [eval, formalDerivative] using hasDerivAt_const (x axis) (0 : ℝ)
  | cons k ks ih =>
      convert (hasDerivAt_monomial_axis (e k) (c k) axis x).add ih using 1 <;>
        simp only [eval, formalDerivative]
      funext t
      rfl

/-- Coordinate partial derivative, defined using the actual one-variable derivative.
The other two coordinates are fixed; the differentiated coordinate is replaced by `t`. -/
def axisDeriv (f : (Fin 3 → ℝ) → ℝ) (axis : Fin 3) (x : Fin 3 → ℝ) : ℝ :=
  deriv (fun t : ℝ => f (Function.update x axis t)) (x axis)

theorem axisDeriv_eval {ι : Type*} (e : ι → Exp3) (c : ι → ℝ)
    (axis : Fin 3) (x : Fin 3 → ℝ) (s : List ι) :
    axisDeriv (fun y => eval e c y s) axis x = formalDerivative e c axis x s := by
  exact (hasDerivAt_eval_axis e c axis x s).deriv

/-- Analytic differentiation of the first formal derivative gives the formal Hessian.
For `i = j`, the second zero guard is applied after the exponent has been lowered. -/
theorem hasDerivAt_formalDerivative_axis {ι : Type*}
    (e : ι → Exp3) (c : ι → ℝ) (i j : Fin 3)
    (x : Fin 3 → ℝ) (s : List ι) :
    HasDerivAt (fun t : ℝ => formalDerivative e c i (Function.update x j t) s)
      (formalHessianEntry e c i j x s) (x j) := by
  exact hasDerivAt_eval_axis (fun k => lowerExponent i (e k))
    (fun k => derivativeCoeff i (e k) (c k)) j x s

theorem axisDeriv_formalDerivative {ι : Type*}
    (e : ι → Exp3) (c : ι → ℝ) (i j : Fin 3)
    (x : Fin 3 → ℝ) (s : List ι) :
    axisDeriv (fun y => formalDerivative e c i y s) j x =
      formalHessianEntry e c i j x s := by
  exact (hasDerivAt_formalDerivative_axis e c i j x s).deriv

/-- Differentiate the actual first partial derivative, not just its formal expression. -/
theorem hasDerivAt_axisDeriv_eval {ι : Type*}
    (e : ι → Exp3) (c : ι → ℝ) (i j : Fin 3)
    (x : Fin 3 → ℝ) (s : List ι) :
    HasDerivAt
      (fun t : ℝ => axisDeriv (fun y => eval e c y s) i (Function.update x j t))
      (formalHessianEntry e c i j x s) (x j) := by
  have hfun :
      (fun t : ℝ => axisDeriv (fun y => eval e c y s) i (Function.update x j t)) =
      (fun t : ℝ => formalDerivative e c i (Function.update x j t) s) := by
    funext t
    exact axisDeriv_eval e c i (Function.update x j t) s
  rw [hfun]
  exact hasDerivAt_formalDerivative_axis e c i j x s

/-- Actual iterated coordinate derivatives agree with the formal Hessian evaluator. -/
theorem axisDeriv_axisDeriv_eval {ι : Type*}
    (e : ι → Exp3) (c : ι → ℝ) (i j : Fin 3)
    (x : Fin 3 → ℝ) (s : List ι) :
    axisDeriv (axisDeriv (fun y => eval e c y s) i) j x =
      formalHessianEntry e c i j x s := by
  exact (hasDerivAt_axisDeriv_eval e c i j x s).deriv

/-- Signed interval evaluation now encloses actual iterated coordinate derivatives. -/
theorem axisDeriv_axisDeriv_eval_mem {ι : Type*}
    (e : ι → Exp3) (C : ι → RatInterval) (c : ι → ℝ) (i j : Fin 3)
    (P : Fin 3 → ℕ → RatInterval) (x : Fin 3 → ℝ)
    (hC : ∀ k, (C k).mem (c k)) (hP : PowerEnclosures P x) (s : List ι) :
    (formalHessianInterval e C i j P s).mem
      (axisDeriv (axisDeriv (fun y => eval e c y s) i) j x) := by
  rw [axisDeriv_axisDeriv_eval]
  exact formalHessianEntry_mem e C c i j P x hC hP s

/-- A saved target interval encloses the actual coordinate Hessian entry once its
endpoint containment of the exact evaluator is established. -/
theorem axisDeriv_axisDeriv_eval_mem_of_bounds {ι : Type*}
    (e : ι → Exp3) (C : ι → RatInterval) (c : ι → ℝ) (i j : Fin 3)
    (P : Fin 3 → ℕ → RatInterval) (x : Fin 3 → ℝ)
    (hC : ∀ k, (C k).mem (c k)) (hP : PowerEnclosures P x) (s : List ι)
    (K : RatInterval) (hlo : K.lo ≤ (formalHessianInterval e C i j P s).lo)
    (hhi : (formalHessianInterval e C i j P s).hi ≤ K.hi) :
    K.mem (axisDeriv (axisDeriv (fun y => eval e c y s) i) j x) := by
  rw [axisDeriv_axisDeriv_eval]
  exact formalHessianEntry_mem_of_bounds e C c i j P x hC hP s K hlo hhi

end ThomsonNine.Interval.SparsePolynomial
