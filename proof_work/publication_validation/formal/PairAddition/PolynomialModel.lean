import PairAddition.CoefficientData
import PairAddition.MatrixModel

noncomputable section
namespace ThomsonNine.PairAddition
open Polynomial
open scoped BigOperators

theorem eval_ofFn (n : ℕ) (c : Fin n → ℝ) (x : ℝ) :
    (Polynomial.ofFn n c).eval x=∑ i : Fin n, c i*x^i.val := by
  rw [Polynomial.ofFn_eq_sum_monomial]
  simp only [Polynomial.eval_finsetSum,Polynomial.eval_monomial]

theorem P_coeff (n : ℕ) : P.coeff n=if hn : n<38 then (pCoefficient ⟨n,hn⟩ : ℝ) else 0 := by
  by_cases hn : n<38
  · simp [P,hn]
  · rw [dif_neg hn]
    exact Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega)

theorem scaled_hasse (h : Fin 38) : C (denominator h : ℝ)*hasseDeriv h.val P=
    Polynomial.ofFn 38 (fun i => (diagonal h i : ℝ)) := by
  ext n
  rw [coeff_C_mul,hasseDeriv_coeff,P_coeff]
  by_cases hn : n<38
  · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ hn]
    have hr := diagonal_relation h ⟨n,hn⟩
    by_cases hnh : n+h.val<38
    · simp only [Fin.val_mk,dif_pos hnh] at hr ⊢
      have he := congrArg (fun q : ℚ => (q : ℝ)) hr
      push_cast at he
      simpa only [mul_assoc] using he.symm
    · simp only [Fin.val_mk,dif_neg hnh,mul_zero] at hr ⊢
      exact_mod_cast hr.symm
  · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega),dif_neg (by omega)]
    simp

theorem scaled_hasse_eval (h : Fin 38) (z : ℝ) :
    (denominator h : ℝ)*(hasseDeriv h.val P).eval z=
      ∑ i : Fin 38, (diagonal h i : ℝ)*z^i.val := by
  have he := congrArg (fun q : ℝ[X] => q.eval z) (scaled_hasse h)
  simpa only [eval_mul,eval_C,eval_ofFn] using he

theorem coefficient_matrix_eval (h : Fin 38) (u v : ℝ) :
    ((contributions h).map (fun c => (c.weight : ℝ)*(IntegerListPolynomial.realPolynomial c.coefficients).eval u*
      (IntegerListPolynomial.realPolynomial c.coefficients).eval v)).sum=
      (denominator h : ℝ)*(hasseDeriv h.val P).eval (u*v) := by
  have hl (c : Contribution) (hc : c∈contributions h) : c.coefficients.length≤38 :=
    of_decide_eq_true (List.all_eq_true.mp (coefficient_lengths h) c hc)
  rw [diagonal_matrix_eval (contributions h) (diagonal h) hl (all_matrices h) u v]
  exact (scaled_hasse_eval h (u*v)).symm

theorem P_shifted_eval (z w : ℝ) : P.eval (w+z)=
    ∑ h : Fin 38, (hasseDeriv h.val P).eval z*w^h.val := by
  have hd : (taylor z P).natDegree<38 := by
    rw [natDegree_taylor]
    exact Polynomial.ofFn_natDegree_lt (by norm_num) _
  rw [← taylor_eval]
  have he := (taylor z P).eval_eq_sum_range' hd w
  rw [← Fin.sum_univ_eq_sum_range] at he
  simpa only [taylor_coeff] using he
end ThomsonNine.PairAddition
