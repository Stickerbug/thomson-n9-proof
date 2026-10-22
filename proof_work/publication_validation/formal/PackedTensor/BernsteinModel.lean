import PackedTensor.RowMatrix
import ThomsonNine.LeafSemantics
import Mathlib.Algebra.BigOperators.Field

noncomputable section
namespace ThomsonNine.PackedTensor
open scoped BigOperators
open ThomsonNine.Semantics

def basisSpec (n : ℕ) : Prop :=
  (∀ j : Fin (n+1), ∀ s : ℝ,
    (∑ i : Fin (n+1), (weight i.val 0 j.val : ℝ)*bernstein n i.val s)=bernstein n j.val (s/2)) ∧
  (∀ j : Fin (n+1), ∀ s : ℝ,
    (∑ i : Fin (n+1), (weight (n-i.val) i.val j.val : ℝ)*bernstein n i.val s)=bernstein n j.val ((1+s)/2))

def curve (n : ℕ) (b : Fin (n+1) → ℝ) (s : ℝ) : ℝ :=
  ∑ j, b j*bernstein n j.val s

theorem left_curve (n : ℕ) (hr : rowSpec (n+1)) (hb : basisSpec n)
    (b : ℕ → ℝ) (s : ℝ) :
    (∑ i : Fin (n+1), realRow b i.val 0*bernstein n i.val s)=
      curve n (fun j => b j.val) (s/2) := by
  have hi (i : Fin (n+1)) : i.val+0<n+1 := by omega
  simp_rw [realRow_matrix (n+1) hr b _ 0 (hi _)]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    (∑ i : Fin (n+1), (weight i.val 0 j.val : ℝ)*b j.val*bernstein n i.val s)=
      b j.val*(∑ i : Fin (n+1), (weight i.val 0 j.val : ℝ)*bernstein n i.val s) := by
        rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro i hi;ring
    _ = _ := by rw [hb.1 j s]

theorem right_curve (n : ℕ) (hr : rowSpec (n+1)) (hb : basisSpec n)
    (b : ℕ → ℝ) (s : ℝ) :
    (∑ i : Fin (n+1), realRow b (n-i.val) i.val*bernstein n i.val s)=
      curve n (fun j => b j.val) ((1+s)/2) := by
  have hi (i : Fin (n+1)) : n-i.val+i.val<n+1 := by omega
  simp_rw [realRow_matrix (n+1) hr b _ _ (hi _)]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    (∑ i : Fin (n+1), (weight (n-i.val) i.val j.val : ℝ)*b j.val*bernstein n i.val s)=
      b j.val*(∑ i : Fin (n+1), (weight (n-i.val) i.val j.val : ℝ)*bernstein n i.val s) := by
        rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro i hi;ring
    _ = _ := by rw [hb.2 j s]
end ThomsonNine.PackedTensor
