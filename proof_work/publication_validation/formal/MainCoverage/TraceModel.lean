import MainCoverage.TraceFields
import MainCoverage.MiddleModel
import Algebra.MonomialSymmetry

set_option maxRecDepth 100000
noncomputable section
namespace ThomsonNine.MainEnvelope.Archive
open scoped BigOperators
open ThomsonNine

theorem diagonal_eq_polynomial (t : ℝ) : diagonal t=∑ k : Fin 21, (diagonalCoeff k : ℝ)*t^k.val := by
  let c := fun j : ℕ => (symMid (Fin.ofNat 756 j) : ℝ)
  let sm := fun j : ℕ => QPolynomial.monomial (ActualF.Data.support (Fin.ofNat 756 j)) 1 t t
  have hm : ∀ k∈List.finRange 21, ∀ j∈diagonalGroups k, sm j=t^k.val := by
    intro k hk j hj
    have hb := (List.all_eq_true.mp (diagonal_exponents k)) j hj
    have he := of_decide_eq_true hb
    simp only [sm,QPolynomial.monomial,one_pow,one_mul,← pow_add,he]
  have hp := FiniteCollector.partition_of_fuel_sorted diagonal_sorted
  have hh := FiniteCollector.collected_eval (List.finRange 21) diagonalGroups 756 c sm (fun k => t^k.val) hp hm
  have hd (k : Fin 21) : (diagonalCoeff k : ℝ)=((diagonalGroups k).map c).sum := by
    have he := congrArg (fun q : ℚ => (q : ℝ)) (diagonal_coefficients k)
    push_cast at he
    simpa only [c,List.map_map,Function.comp_def] using he
  simp_rw [← hd] at hh
  rw [MonomialSymmetry.finRange_sum] at hh
  let fn := fun j : ℕ => c j*sm j
  have hNat : ((List.range 756).map fn).sum=∑ j∈Finset.range 756, fn j := by
    simpa only [List.toFinset_range] using (List.sum_toFinset fn (show (List.range 756).Nodup from List.nodup_range)).symm
  have hFin : (∑ j : Fin 756, fn j.val)=middlePolynomial ![1,t,t] := by
    unfold middlePolynomial
    apply Finset.sum_congr rfl
    intro j hj
    simp only [fn,c,sm,Fin.ofNat_val_eq_self,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  have hr : ((List.range 756).map (fun j => c j*sm j)).sum=middlePolynomial ![1,t,t] :=
    hNat.trans ((Fin.sum_univ_eq_sum_range fn 756).symm.trans hFin)
  rw [hr] at hh
  unfold diagonal
  rw [middle_eq_polynomial]
  exact hh.symm
end ThomsonNine.MainEnvelope.Archive
