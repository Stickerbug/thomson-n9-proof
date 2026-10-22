import ThomsonNine.IntervalSparseDerivative
import Mathlib.Analysis.Calculus.Deriv.Shift

noncomputable section
namespace ThomsonNine.Interval.SparsePolynomial

def translate (a : Fin 3 → ℝ) (f : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  f (fun j => a j + x j)

/-- Coordinate derivatives commute with a fixed translation, even at points
where the total deriv operator takes its default value. -/
theorem axisDeriv_translate (f : (Fin 3 → ℝ) → ℝ) (a : Fin 3 → ℝ)
    (i : Fin 3) (x : Fin 3 → ℝ) :
    axisDeriv (translate a f) i x =
      axisDeriv f i (fun j => a j + x j) := by
  unfold axisDeriv translate
  have hupdate : (fun t : ℝ => f (fun j => a j + Function.update x i t j)) =
      (fun t : ℝ => f (Function.update (fun j => a j + x j) i (a i+t))) := by
    funext t
    congr 1
    funext j
    by_cases h : j = i <;> simp [h, Function.update_apply]
  rw [hupdate]
  exact deriv_comp_const_add (fun z => f (Function.update (fun j => a j+x j) i z)) (a i) (x i)

 theorem axisDeriv_axisDeriv_translate (f : (Fin 3 → ℝ) → ℝ) (a : Fin 3 → ℝ)
    (i j : Fin 3) (x : Fin 3 → ℝ) :
    axisDeriv (axisDeriv (translate a f) j) i x =
      axisDeriv (axisDeriv f j) i (fun k => a k + x k) := by
  have hfun : axisDeriv (translate a f) j = translate a (axisDeriv f j) := by
    funext y
    exact axisDeriv_translate f a j y
  rw [hfun, axisDeriv_translate]
end ThomsonNine.Interval.SparsePolynomial
