import ThomsonNine.AAACollected
import ThomsonNine.Construction.LocalShift.Metadata
import ThomsonNine.Construction.Kernel.FeatureExpansion

-- Isolated source: LocalShift.Model
set_option maxRecDepth 100000
noncomputable section
namespace ThomsonNine.LocalShift
open ThomsonNine.LocalSparseHessianAAA ThomsonNine.GatheredBinding
open ThomsonNine.Interval.SparsePolynomial ThomsonNine.ListPolynomial
open ThomsonNine.MonomialSymmetry
open scoped BigOperators
attribute [local irreducible] rows base rowOf

theorem row_binding (axis : Fin 3) (t : TermIndex) :
    exponents t axis<(rows axis (rowOf axis t)).length ∧
    (rows axis (rowOf axis t))[exponents t axis]?=some t := by
  have ht : t∈(List.finRange 155).flatMap (rows axis) :=
    (rows_partition axis).mem_iff.mpr (AAAGroupedData.allTerms_complete t)
  obtain ⟨r,hr,ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨n,hn,hv⟩ := List.mem_iff_getElem.mp ht
  have hi := row_inverse axis r ⟨n,hn⟩
  have he := row_shape axis r ⟨n,hn⟩ axis
  rw [hv] at hi he
  simp only [ite_true] at he
  rw [hi,he]
  exact ⟨hn,by rw [List.getElem?_eq_getElem hn,hv]⟩

def step (axis : Fin 3) (a : ℝ) (c : TermIndex → ℝ) (t : TermIndex) : ℝ :=
  (polynomial (HornerShift.shifted a ((rows axis (rowOf axis t)).map c))).coeff (exponents t axis)

theorem step_row (axis : Fin 3) (row : Fin 155) (a : ℝ) (c : TermIndex → ℝ) :
    (rows axis row).map (step axis a c)=HornerShift.shifted a ((rows axis row).map c) := by
  apply List.ext_getElem
  · simp only [List.length_map,HornerShift.shifted_length]
  · intro n hn1 hn2
    have hn : n<(rows axis row).length := by simpa only [List.length_map] using hn1
    have hi := row_inverse axis row ⟨n,hn⟩
    have he := row_shape axis row ⟨n,hn⟩ axis
    simp only [ite_true] at he
    simp only [List.getElem_map]
    rw [step,hi,he,polynomial_coeff,List.getElem?_eq_getElem hn2]
    rfl

theorem row_monomial (axis : Fin 3) (row : Fin 155) (k : Fin (rows axis row).length) (x : Fin 3 → ℝ) :
    monomial (exponents ((rows axis row)[k.val])) x=monomial (base axis row) x*(x axis)^k.val := by
  have he : exponents ((rows axis row)[k.val])=(fun a => if a=axis then k.val else base axis row a) := by
    funext a
    exact row_shape axis row k a
  rw [he]
  fin_cases axis <;> simp [monomial,row_base_zero] <;> ring

theorem polynomial_map_eval {α : Type*} (l : List α) (c : α → ℝ) (x : ℝ) :
    (polynomial (l.map c)).eval x=∑ i : Fin l.length, c (l[i.val])*x^i.val := by
  induction l with
  | nil => simp [polynomial]
  | cons a l ih =>
    simp only [List.map_cons,polynomial,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_X,
      List.length_cons,Fin.sum_univ_succ,Fin.val_zero,List.getElem_cons_zero,pow_zero,mul_one,
      Fin.val_succ,List.getElem_cons_succ]
    rw [ih,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [pow_succ]
    ring

theorem row_eval (axis : Fin 3) (row : Fin 155) (c : TermIndex → ℝ) (x : Fin 3 → ℝ) :
    ((rows axis row).map (fun t => c t*monomial (exponents t) x)).sum=
      monomial (base axis row) x*(polynomial ((rows axis row).map c)).eval (x axis) := by
  rw [← list_indexed_sum (rows axis row) .t000 (fun t => c t*monomial (exponents t) x),finRange_sum]
  rw [polynomial_map_eval,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [List.getElem?_eq_getElem k.isLt]
  simp only [Option.getD_some]
  rw [row_monomial]
  ring

theorem eval_rows (axis : Fin 3) (c : TermIndex → ℝ) (x : Fin 3 → ℝ) :
    eval exponents c x allTerms=∑ row : Fin 155,
      monomial (base axis row) x*(polynomial ((rows axis row).map c)).eval (x axis) := by
  rw [AAACollected.eval_eq_map_sum]
  have hp := List.Perm.sum_eq ((rows_partition axis).map (fun t => c t*monomial (exponents t) x))
  rw [← hp,flatMap_sum_map,finRange_sum]
  exact Finset.sum_congr rfl (fun row _ => row_eval axis row c x)

theorem base_update (axis : Fin 3) (row : Fin 155) (x : Fin 3 → ℝ) (a : ℝ) :
    monomial (base axis row) (Function.update x axis a)=monomial (base axis row) x := by
  fin_cases axis <;> simp [monomial,row_base_zero]

theorem step_eval (axis : Fin 3) (a : ℝ) (c : TermIndex → ℝ) (x : Fin 3 → ℝ) :
    eval exponents (step axis a c) x allTerms=
      eval exponents c (Function.update x axis (a+x axis)) allTerms := by
  rw [eval_rows axis,eval_rows axis]
  apply Finset.sum_congr rfl
  intro row hrow
  rw [step_row,HornerShift.shifted_eval,base_update]
  simp
end ThomsonNine.LocalShift
