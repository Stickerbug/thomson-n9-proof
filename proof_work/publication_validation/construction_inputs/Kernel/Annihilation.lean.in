import ThomsonNine.Construction.Kernel.Syzygy
import ThomsonNine.Construction.Matrices.Model

-- Isolated source: Kernel.Annihilation
noncomputable section
namespace ThomsonNine.ActualKernel.Syzygy
open ThomsonNine.CertificateMatrices ThomsonNine.RationalListPolynomial Polynomial
open scoped BigOperators

theorem padded_p : ∀ k j : Fin 11, ambientDim k≤j.val → p k j=[] := by decide +kernel
theorem padded_c : ∀ k j : Fin 11, ambientDim k≤j.val → c k j=[] := by decide +kernel

theorem sum_ambient (k : Fin 11) (f : Fin 11 → ℝ) (hz : ∀ j, ambientDim k≤j.val → f j=0) :
    ∑ a : Fin (ambientDim k), f (ambientIndex k a)=∑ j : Fin 11, f j := by
  refine Fintype.sum_of_injective (ambientIndex k) ?_ _ _ ?_ (fun _ => rfl)
  · intro a b h
    apply Fin.ext
    exact congrArg (fun j : Fin 11 => j.val) h
  · intro j hj
    apply hz
    by_contra! h
    apply hj
    exact ⟨⟨j.val,h⟩,Fin.ext rfl⟩

def pVector (k : Fin 11) (r : ℝ) (a : Fin (ambientDim k)) : ℝ :=
    (realPolynomial (p k (ambientIndex k a))).eval r
def cVector (k : Fin 11) (r : ℝ) (a : Fin (ambientDim k)) : ℝ :=
    (realPolynomial (c k (ambientIndex k a))).eval r

theorem transpose_N_p (k : Fin 11) :
    Matrix.mulVec (CertificateMatrices.N k).transpose (pVector k RefinedRadius.radius)=0 := by
  funext i
  change (∑ a : Fin (ambientDim k), ActualKernel.N k (reducedIndex k i) (ambientIndex k a)*pVector k RefinedRadius.radius a)=0
  simp only [pVector]
  rw [sum_ambient k (fun j => ActualKernel.N k (reducedIndex k i) j*(realPolynomial (p k j)).eval RefinedRadius.radius)
    (fun j hj => by rw [padded_p k j hj]; simp)]
  simpa only [mul_comm] using p_annihilates_N k (reducedIndex k i)
theorem transpose_N_c (k : Fin 11) :
    Matrix.mulVec (CertificateMatrices.N k).transpose (cVector k RefinedRadius.radius)=0 := by
  funext i
  change (∑ a : Fin (ambientDim k), ActualKernel.N k (reducedIndex k i) (ambientIndex k a)*cVector k RefinedRadius.radius a)=0
  simp only [cVector]
  rw [sum_ambient k (fun j => ActualKernel.N k (reducedIndex k i) j*(realPolynomial (c k j)).eval RefinedRadius.radius)
    (fun j hj => by rw [padded_c k j hj]; simp)]
  simpa only [mul_comm] using c_annihilates_N k (reducedIndex k i)

theorem A_p_zero (X : Fin 190 → ℝ) (k : Fin 11) :
    Matrix.mulVec (A X k) (pVector k RefinedRadius.radius)=0 := by
  simp only [A,← Matrix.mulVec_mulVec,transpose_N_p,Matrix.mulVec_zero]
theorem A_c_zero (X : Fin 190 → ℝ) (k : Fin 11) :
    Matrix.mulVec (A X k) (cVector k RefinedRadius.radius)=0 := by
  simp only [A,← Matrix.mulVec_mulVec,transpose_N_c,Matrix.mulVec_zero]
end ThomsonNine.ActualKernel.Syzygy
