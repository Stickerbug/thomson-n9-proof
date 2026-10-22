import Mathlib.LinearAlgebra.Lagrange
import ThomsonNine.HermiteFactor

noncomputable section
namespace ThomsonNine.HermiteInterpolation
open Polynomial
open scoped BigOperators

variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]

def basis (xi : I → K) (i : I) : K[X] := Lagrange.basis Finset.univ xi i

def valueBasis (xi : I → K) (i : I) : K[X] :=
  (1-C (2*(basis xi i).derivative.eval (xi i))*(X-C (xi i))) * (basis xi i)^2

def derivativeBasis (xi : I → K) (i : I) : K[X] :=
  (X-C (xi i))*(basis xi i)^2

def interpolate (xi v d : I → K) : K[X] :=
  ∑ i, (C (v i)*valueBasis xi i + C (d i)*derivativeBasis xi i)

lemma basis_eval_self (xi : I → K) (hxi : Function.Injective xi) (i : I) :
    (basis xi i).eval (xi i) = 1 :=
  Lagrange.eval_basis_self (fun a _ b _ h => hxi h) (Finset.mem_univ i)

lemma basis_eval_ne (xi : I → K) (i j : I) (hij : i ≠ j) :
    (basis xi i).eval (xi j) = 0 :=
  Lagrange.eval_basis_of_ne hij (Finset.mem_univ j)

 theorem valueBasis_eval (xi : I → K) (hxi : Function.Injective xi) (i j : I) :
    (valueBasis xi i).eval (xi j) = if i=j then 1 else 0 := by
  by_cases h : i=j
  · subst j
    simp [valueBasis,basis_eval_self xi hxi]
  · simp [valueBasis,basis_eval_ne xi i j h,h]

 theorem derivativeBasis_eval (xi : I → K) (hxi : Function.Injective xi) (i j : I) :
    (derivativeBasis xi i).eval (xi j) = 0 := by
  by_cases h : i=j
  · subst j; simp [derivativeBasis]
  · simp [derivativeBasis,basis_eval_ne xi i j h]

 theorem valueBasis_derivative_eval (xi : I → K) (hxi : Function.Injective xi) (i j : I) :
    (valueBasis xi i).derivative.eval (xi j) = 0 := by
  by_cases h : i=j
  · subst j
    simp [valueBasis,pow_two,derivative_mul,basis_eval_self xi hxi]
    ring
  · simp [valueBasis,pow_two,derivative_mul,basis_eval_ne xi i j h]

 theorem derivativeBasis_derivative_eval (xi : I → K) (hxi : Function.Injective xi) (i j : I) :
    (derivativeBasis xi i).derivative.eval (xi j) = if i=j then 1 else 0 := by
  by_cases h : i=j
  · subst j
    simp [derivativeBasis,pow_two,derivative_mul,basis_eval_self xi hxi]
  · simp [derivativeBasis,pow_two,derivative_mul,basis_eval_ne xi i j h,h]

 theorem interpolate_eval (xi v d : I → K) (hxi : Function.Injective xi) (j : I) :
    (interpolate xi v d).eval (xi j) = v j := by
  classical
  simp [interpolate, eval_finsetSum, valueBasis_eval xi hxi, derivativeBasis_eval xi hxi]

 theorem interpolate_derivative_eval (xi v d : I → K) (hxi : Function.Injective xi) (j : I) :
    (interpolate xi v d).derivative.eval (xi j) = d j := by
  classical
  simp [interpolate,derivative_sum,derivative_mul,eval_finsetSum,
    valueBasis_derivative_eval xi hxi,derivativeBasis_derivative_eval xi hxi]

lemma basis_natDegree (xi : I → K) (hxi : Function.Injective xi) (i : I) :
    (basis xi i).natDegree = Fintype.card I - 1 :=
  Lagrange.natDegree_basis (fun a _ b _ h => hxi h) (Finset.mem_univ i)

theorem valueBasis_natDegree (xi : I → K) (hxi : Function.Injective xi) (i : I) :
    (valueBasis xi i).natDegree ≤ 1+2*(Fintype.card I-1) := by
  have hlin : (1-C (2*(basis xi i).derivative.eval (xi i))*(X-C (xi i))).natDegree ≤ 1 := by
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · simp
    · have h : (C (2*(basis xi i).derivative.eval (xi i))*(X-C (xi i))).natDegree ≤
          (C (2*(basis xi i).derivative.eval (xi i))).natDegree+(X-C (xi i)).natDegree := natDegree_mul_le
      simpa only [natDegree_C,natDegree_X_sub_C,zero_add] using h
  have h : (valueBasis xi i).natDegree ≤
      (1-C (2*(basis xi i).derivative.eval (xi i))*(X-C (xi i))).natDegree+
        ((basis xi i)^2).natDegree := natDegree_mul_le
  rw [natDegree_pow,basis_natDegree xi hxi i] at h
  omega

theorem derivativeBasis_natDegree (xi : I → K) (hxi : Function.Injective xi) (i : I) :
    (derivativeBasis xi i).natDegree ≤ 1+2*(Fintype.card I-1) := by
  have h : (derivativeBasis xi i).natDegree ≤ (X-C (xi i)).natDegree+
      ((basis xi i)^2).natDegree := natDegree_mul_le
  simpa only [natDegree_X_sub_C,natDegree_pow,basis_natDegree xi hxi i] using h

theorem interpolate_natDegree (xi v d : I → K) (hxi : Function.Injective xi) :
    (interpolate xi v d).natDegree ≤ 1+2*(Fintype.card I-1) := by
  apply natDegree_sum_le_of_forall_le
  intro i hi
  apply (natDegree_add_le _ _).trans
  apply max_le
  · have h : (C (v i)*valueBasis xi i).natDegree ≤ (C (v i)).natDegree+(valueBasis xi i).natDegree := natDegree_mul_le
    simp only [natDegree_C,zero_add] at h
    exact h.trans (valueBasis_natDegree xi hxi i)
  · have h : (C (d i)*derivativeBasis xi i).natDegree ≤ (C (d i)).natDegree+(derivativeBasis xi i).natDegree := natDegree_mul_le
    simp only [natDegree_C,zero_add] at h
    exact h.trans (derivativeBasis_natDegree xi hxi i)


/-- The logarithmic-derivative sum at a Lagrange node avoids expanding and
re-evaluating the full derivative polynomial in the numeric certificate. -/
theorem basis_derivative_at_node (xi : I → K) (hxi : Function.Injective xi) (i : I) :
    (basis xi i).derivative.eval (xi i) = ∑ j ∈ Finset.univ.erase i, (xi i-xi j)⁻¹ := by
  unfold basis Lagrange.basis
  rw [derivative_prod_finset,eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [eval_mul,eval_prod]
  have hp : (∏ k ∈ (Finset.univ.erase i).erase j,
      (Lagrange.basisDivisor (xi i) (xi k)).eval (xi i)) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    exact Lagrange.eval_basisDivisor_left_of_ne (fun h => hki (hxi h).symm)
  rw [hp]
  simp [Lagrange.basisDivisor,derivative_C_mul,derivative_X_sub_C]
end ThomsonNine.HermiteInterpolation
