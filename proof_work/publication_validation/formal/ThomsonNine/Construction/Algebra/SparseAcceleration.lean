import ThomsonNine.Construction.Algebra.SparseCurve

-- Isolated source: Algebra.SparseAcceleration
noncomputable section
namespace ThomsonNine.Interval.SparsePolynomial
open scoped BigOperators
theorem variable_directionalDerivative_curve {α : Type*} (e : α → Exp3) (c : α → ℝ) (l : List α)
    (curve velocity : ℝ → (Fin 3 → ℝ)) (acceleration : Fin 3 → ℝ) (s : ℝ)
    (hd : ∀ i, HasDerivAt (fun t => curve t i) (velocity s i) s)
    (hdd : ∀ i, HasDerivAt (fun t => velocity t i) (acceleration i) s) :
    HasDerivAt (fun t => directionalDerivative e c (curve t) (velocity t) l)
      (directionalHessian e c (curve s) (velocity s) l+
        directionalDerivative e c (curve s) acceleration l) s := by
  have h (i : Fin 3) :=
    (eval_curve_derivative (fun k => lowerExponent i (e k)) (fun k => derivativeCoeff i (e k) (c k))
      l curve (velocity s) s hd).mul (hdd i)
  have hsum := HasDerivAt.fun_sum (u:=Finset.univ) (fun i _ => h i)
  convert hsum using 1
  · rfl
  · simp only [directionalHessian,directionalDerivative,formalHessianEntry,formalDerivative,
      Finset.sum_mul,Finset.sum_add_distrib]
end ThomsonNine.Interval.SparsePolynomial
