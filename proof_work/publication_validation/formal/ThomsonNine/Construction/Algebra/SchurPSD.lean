import ThomsonNine.Construction.Algebra.SchurSolve
import Mathlib.LinearAlgebra.Matrix.PosDef

-- Isolated source: Algebra.SchurPSD
noncomputable section
namespace ThomsonNine.SchurSolve
open scoped BigOperators
open Matrix

theorem reducedMatrix_symmetric {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hA : ∀ i j, A i j=A j i) : ∀ i j, reducedMatrix A i j=reducedMatrix A j i := by
  intro i j
  simp only [reducedMatrix]
  rw [hA i.succ j.succ,hA i.succ 0,hA j.succ 0]
  ring

theorem quadratic_schur {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hA : ∀ i j, A i j=A j i) (hp : A 0 0≠0) (x : Fin (n+1) → ℝ) :
    x ⬝ᵥ A.mulVec x =
      A 0 0*(x 0+(A 0 0)⁻¹*(∑ j : Fin n, A 0 j.succ*x j.succ))^2+
      (fun i : Fin n => x i.succ) ⬝ᵥ (reducedMatrix A).mulVec (fun i => x i.succ) := by
  let S := ∑ j : Fin n, A 0 j.succ*x j.succ
  let T := ∑ i : Fin n, ∑ j : Fin n, x i.succ*A i.succ j.succ*x j.succ
  have htail : (fun i : Fin n => x i.succ) ⬝ᵥ (reducedMatrix A).mulVec (fun i => x i.succ) =
      T-(A 0 0)⁻¹*S^2 := by
    dsimp [S,T]
    simp only [dotProduct,mulVec,reducedMatrix,Finset.mul_sum,sub_mul,mul_sub,Finset.sum_sub_distrib]
    rw [pow_two,Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    · apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hA i.succ 0]
      ring
  have hcross : (∑ i : Fin n, x i.succ*A i.succ 0)=S := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hA i.succ 0]
    ring
  have hfull : x ⬝ᵥ A.mulVec x = A 0 0*(x 0)^2+2*x 0*S+T := by
    have h1 : (∑ i : Fin n, x i.succ*(A i.succ 0*x 0)) = x 0*S := by
      rw [← hcross,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have h2 : (∑ i : Fin n, x i.succ*(∑ j : Fin n, A i.succ j.succ*x j.succ))=T := by
      dsimp [T]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    simp only [dotProduct,mulVec,Fin.sum_univ_succ]
    change x 0*(A 0 0*x 0+S)+(∑ i : Fin n, x i.succ*(A i.succ 0*x 0+(∑ j : Fin n, A i.succ j.succ*x j.succ))) = _
    rw [show (∑ i : Fin n, x i.succ*(A i.succ 0*x 0+(∑ j : Fin n, A i.succ j.succ*x j.succ)))=x 0*S+T by
      simp only [mul_add,Finset.sum_add_distrib]
      rw [h1,h2]]
    ring
  rw [hfull,htail]
  change _ = A 0 0*(x 0+(A 0 0)⁻¹*S)^2+(T-(A 0 0)⁻¹*S^2)
  field_simp [hp]
  ring

theorem psd_of_reduced {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hA : ∀ i j, A i j=A j i) (hp : 0<A 0 0) (hR : (reducedMatrix A).PosSemidef) :
    A.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simpa using hA j i
  · intro x
    simp only [star_trivial]
    rw [quadratic_schur A hA (ne_of_gt hp)]
    exact add_nonneg (mul_nonneg (le_of_lt hp) (sq_nonneg _))
      (by simpa only [star_trivial] using hR.dotProduct_mulVec_nonneg (fun i => x i.succ))
end ThomsonNine.SchurSolve
