import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import ThomsonNine.Interval
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

noncomputable section
namespace ThomsonNine.SchurSolve
open scoped BigOperators
open Matrix

def reducedMatrix {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => A i.succ j.succ-A i.succ 0*(A 0 0)⁻¹*A 0 j.succ
def reducedRhs {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (b : Fin (n+1) → ℝ) :
    Fin n → ℝ := fun i => b i.succ-A i.succ 0*(A 0 0)⁻¹*b 0
def recover {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (b : Fin (n+1) → ℝ)
    (tail : Fin n → ℝ) : Fin (n+1) → ℝ :=
  Fin.cons ((A 0 0)⁻¹*(b 0-∑ j, A 0 j.succ*tail j)) tail

theorem row_cons {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (head : ℝ) (tail : Fin n → ℝ) (i : Fin (n+1)) :
    (A.mulVec (Fin.cons head tail)) i = A i 0*head+∑ j, A i j.succ*tail j := by
  simp only [mulVec,dotProduct,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]

theorem recover_solves {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (b : Fin (n+1) → ℝ) (hp : A 0 0≠0) (tail : Fin n → ℝ)
    (htail : (reducedMatrix A).mulVec tail = reducedRhs A b) :
    A.mulVec (recover A b tail)=b := by
  funext i
  cases i using Fin.cases with
  | zero =>
    rw [recover,row_cons]
    rw [← mul_assoc,mul_inv_cancel₀ hp,one_mul]
    ring
  | succ i =>
    have ht := congrFun htail i
    change (∑ j, (A i.succ j.succ-A i.succ 0*(A 0 0)⁻¹*A 0 j.succ)*tail j) =
      b i.succ-A i.succ 0*(A 0 0)⁻¹*b 0 at ht
    have hs : (∑ j, (A i.succ j.succ-A i.succ 0*(A 0 0)⁻¹*A 0 j.succ)*tail j) =
        (∑ j, A i.succ j.succ*tail j)-A i.succ 0*(A 0 0)⁻¹*(∑ j, A 0 j.succ*tail j) := by
      simp only [sub_mul,Finset.sum_sub_distrib,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hs] at ht
    rw [recover,row_cons]
    linear_combination ht

theorem recover_exists {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (b : Fin (n+1) → ℝ) (hp : A 0 0≠0)
    (h : ∃ tail, (reducedMatrix A).mulVec tail = reducedRhs A b) :
    ∃ x, A.mulVec x=b := by
  obtain ⟨tail,ht⟩ := h
  exact ⟨recover A b tail,recover_solves A b hp tail ht⟩
end ThomsonNine.SchurSolve
