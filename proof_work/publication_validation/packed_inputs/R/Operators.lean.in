import R.GroupSemantics

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
noncomputable section
namespace ThomsonNine.ActualR.Collection
open Polynomial
open scoped BigOperators
open ThomsonNine.MonomialSymmetry

def allIds : List ℕ :=
  (List.finRange 3).flatMap (fun a => (List.finRange 28).map (hId a))++
    (List.finRange 756).map fId++
    (List.finRange 3).flatMap (fun a => (List.finRange 756).map (dId a))++[3108]
theorem allIds_eq_range : allIds=List.range 3109 := by decide +kernel
def operatorEval (u v t : ℝ) (n : ℕ) : ℝ :=
  actualSourceCoefficient n*QPolynomial.monomial (sourceExponent n) u v t
def rawOperatorEval (u v t : ℝ) : ℝ := ((List.range 3109).map (operatorEval u v t)).sum

theorem axis_monomial (a : Fin 3) (n : ℕ) (u v t : ℝ) :
    QPolynomial.monomial (axisExponent a n) u v t=(![u,v,t] a)^n := by
  fin_cases a <;> simp [axisExponent,QPolynomial.monomial]

theorem hIds_sum (a : Fin 3) (u v t : ℝ) :
    ((List.finRange 28).map (fun n => operatorEval u v t (hId a n))).sum =
      ActualHermite.H.eval (![u,v,t] a) := by
  simp only [operatorEval,actualSourceCoefficient,source_h,exponent_h,axis_monomial]
  rw [finRange_sum,Fin.sum_univ_eq_sum_range (fun n => ActualHermite.H.coeff n*(![u,v,t] a)^n)]
  have hp := ActualHermite.H.as_sum_range_C_mul_X_pow' (n := 28)
    (show ActualHermite.H.natDegree<28 by have h := ActualHermite.H_natDegree; omega)
  have he := congrArg (Polynomial.eval (![u,v,t] a)) hp
  simpa only [Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X] using he.symm

theorem fIds_sum (u v t : ℝ) :
    ((List.finRange 756).map (fun j => operatorEval u v t (fId j))).sum =
      -7*ActualF.F X u v t := by
  simp only [operatorEval,actualSourceCoefficient,source_f,exponent_f,mul_assoc]
  rw [map_mul_sum,finRange_sum]
  rfl

theorem dIds_sum (a : Fin 3) (u v t : ℝ) :
    ((List.finRange 756).map (fun j => operatorEval u v t (dId a j))).sum =
      -ActualF.F X 1 (![u,v,t] a) (![u,v,t] a) := by
  let w := ![u,v,t] a
  have he (j : Fin 756) :
      operatorEval u v t (dId a j) =
        -(ActualF.coefficient X j*QPolynomial.monomial (ActualF.Data.support j) 1 w w) := by
    simp only [operatorEval,actualSourceCoefficient,source_d,exponent_d,axis_monomial]
    simp only [QPolynomial.monomial,one_pow,one_mul,pow_add]
    dsimp [w]
    ring
  have hm := List.map_congr_left (fun j (_ : j∈List.finRange 756) => he j)
  rw [hm,map_sum_neg,finRange_sum]
  rfl

theorem cId_eval (u v t : ℝ) : operatorEval u v t 3108= -ActualF.Constants.c X := by
  simp [operatorEval,actualSourceCoefficient,source_c,exponent_c,QPolynomial.monomial]

theorem rawOperatorEval_eq_residual (u v t : ℝ) :
    rawOperatorEval u v t =
      ActualHermite.H.eval u+ActualHermite.H.eval v+ActualHermite.H.eval t-
        7*ActualF.F X u v t-
        ActualF.F X 1 u u-ActualF.F X 1 v v-ActualF.F X 1 t t-ActualF.Constants.c X := by
  have hH : (((List.finRange 3).flatMap (fun a => (List.finRange 28).map (hId a))).map (operatorEval u v t)).sum =
      ∑ a : Fin 3, ActualHermite.H.eval (![u,v,t] a) := by
    rw [flatMap_sum_map]
    simp only [List.map_map,Function.comp_def,hIds_sum]
    exact finRange_sum _ _
  have hF : (((List.finRange 756).map fId).map (operatorEval u v t)).sum= -7*ActualF.F X u v t := by
    simpa only [List.map_map,Function.comp_def] using fIds_sum u v t
  have hD : (((List.finRange 3).flatMap (fun a => (List.finRange 756).map (dId a))).map (operatorEval u v t)).sum =
      ∑ a : Fin 3, -ActualF.F X 1 (![u,v,t] a) (![u,v,t] a) := by
    rw [flatMap_sum_map]
    simp only [List.map_map,Function.comp_def,dIds_sum]
    exact finRange_sum _ _
  have hC : ([3108].map (operatorEval u v t)).sum= -ActualF.Constants.c X := by
    simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using cId_eval u v t
  unfold rawOperatorEval
  rw [← allIds_eq_range,allIds]
  simp only [List.map_append,List.sum_append,hH,hF,hD,hC]
  rw [Fin.sum_univ_three,Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  ring
end ThomsonNine.ActualR.Collection
