import ThomsonNine.ActualHermite
import Mathlib.Algebra.BigOperators.NatAntidiagonal

noncomputable section
namespace ThomsonNine.ActualHermite.QuotientStructure
open Polynomial
open scoped BigOperators

def W : ℝ[X] := ∏ i : Fin 14, (X-C (node i))^2
def Q : ℝ[X] := Classical.choose exists_quotient

theorem factor : HermiteFactor.G H = W*Q := Classical.choose_spec exists_quotient

theorem W_monic : W.Monic := by
  apply monic_prod_of_monic
  intro i hi
  exact (monic_X_sub_C (node i)).pow 2

theorem W_natDegree : W.natDegree = 28 := by
  unfold W
  rw [natDegree_prod]
  · simp [natDegree_pow,natDegree_X_sub_C]
  · intro i hi
    exact pow_ne_zero 2 (monic_X_sub_C (node i)).ne_zero

theorem W_top_coefficient : W.coeff 28 = 1 := by
  simpa only [W_natDegree] using W_monic.coeff_natDegree

theorem G_natDegree : (HermiteFactor.G H).natDegree ≤ 55 := by
  have hd : (C 2-C 2*X : ℝ[X]).natDegree ≤ 1 := by
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · simp
    · have h : (C 2*X : ℝ[X]).natDegree ≤ (C (2 : ℝ)).natDegree+(X : ℝ[X]).natDegree := natDegree_mul_le
      simpa using h
  have hm : ((C 2-C 2*X)*H^2).natDegree ≤
      (C 2-C 2*X : ℝ[X]).natDegree+(H^2).natDegree := natDegree_mul_le
  rw [natDegree_pow] at hm
  have hg : (HermiteFactor.G H).natDegree ≤ max (1 : ℝ[X]).natDegree
      (((C 2-C 2*X)*H^2).natDegree) := natDegree_sub_le _ _
  rw [natDegree_one] at hg
  have hh := H_natDegree
  omega

theorem Q_natDegree : Q.natDegree ≤ 27 := by
  by_cases hQ : Q=0
  · simp [hQ]
  · have hW : W≠0 := W_monic.ne_zero
    have hdegree := natDegree_mul hW hQ
    rw [← factor,W_natDegree] at hdegree
    have h := G_natDegree
    omega

 theorem Q_coefficient_zero {n : ℕ} (hn : 27<n) : Q.coeff n = 0 :=
  coeff_eq_zero_of_natDegree_lt (Q_natDegree.trans_lt hn)

/-- A monic coefficient equation, without any division of real coefficients. -/
theorem monic_quotient_coefficient (A B : ℝ[X]) (d : ℕ) (hd : A.natDegree=d)
    (hA : A.Monic) (n : ℕ) :
    B.coeff n = (A*B).coeff (n+d)-
      ∑ j ∈ Finset.range d, A.coeff j*B.coeff (n+d-j) := by
  have htop : A.coeff d=1 := by simpa only [hd] using hA.coeff_natDegree
  rw [coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => A.coeff i * B.coeff j) (n+d)]
  have htrunc : (∑ j ∈ Finset.range (n+d+1), A.coeff j*B.coeff (n+d-j)) =
      ∑ j ∈ Finset.range (d+1), A.coeff j*B.coeff (n+d-j) := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j hj hjnot
    have hzero : A.coeff j=0 := coeff_eq_zero_of_natDegree_lt (by
      simp only [Finset.mem_range] at hj hjnot
      omega)
    simp [hzero]
  rw [htrunc,Finset.sum_range_succ,htop]
  simp
end ThomsonNine.ActualHermite.QuotientStructure
