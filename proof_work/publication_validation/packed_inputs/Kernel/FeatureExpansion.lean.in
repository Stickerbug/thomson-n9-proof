import Kernel.Annihilation
import Kernel.BasisJet

noncomputable section
namespace ThomsonNine.ActualKernel
open ThomsonNine.ListPolynomial ThomsonNine.RationalListPolynomial Polynomial
open ThomsonNine.CertificateMatrices
open scoped BigOperators

theorem polynomial_eval (l : List ℝ) (x : ℝ) :
    (polynomial l).eval x=∑ i : Fin l.length, l[i.val]*x^i.val := by
  induction l with
  | nil => simp [polynomial]
  | cons a l ih =>
    simp only [polynomial,eval_add,eval_C,eval_mul,eval_X,List.length_cons,Fin.sum_univ_succ,
      Fin.val_zero,List.getElem_cons_zero,pow_zero,mul_one,Fin.val_succ,List.getElem_cons_succ]
    rw [ih,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [pow_succ]
    ring

theorem padded_numerator : ∀ k i j : Fin 11, ambientDim k≤j.val →
    ExactPolynomial.trim (numerator k i j)=[] := by decide +kernel

theorem padded_N (k i j : Fin 11) (hj : ambientDim k≤j.val) : ActualKernel.N k i j=0 := by
  have h := congrArg realPolynomial (padded_numerator k i j hj)
  rw [ExactPolynomial.trim_sound] at h
  simp only [N,numValue,h,RationalListPolynomial.nil,eval_zero,zero_div]

theorem feature_eq_sum (k i : Fin 11) (u : ℝ) :
    BasisJet.feature k i u=∑ a : Fin (ambientDim k), ActualKernel.N k i (ambientIndex k a)*u^a.val := by
  rw [BasisJet.feature,polynomial_eval]
  have he : ∑ a : Fin (ambientDim k), ActualKernel.N k i (ambientIndex k a)*u^a.val =
      ∑ j : Fin 11, ActualKernel.N k i j*u^j.val :=
    Syzygy.sum_ambient k (fun j => ActualKernel.N k i j*u^j.val)
      (fun j hj => by rw [padded_N k i j hj,zero_mul])
  rw [he]
  simp only [BasisJet.coefficients,List.length_map,List.length_finRange,List.getElem_map,List.getElem_finRange]
  apply Finset.sum_congr rfl
  intro j hj
  rfl
end ThomsonNine.ActualKernel
