import ThomsonNine.ThreePointBound
import F.Expansion
import Kernel.FeatureExpansion
import Algebra.MatrixPolynomial

noncomputable section
namespace ThomsonNine.ActualF
open ThomsonNine.CertificateMatrices ThomsonNine.ActualKernel.BasisJet
open ThomsonNine.ThreePoint ThomsonNine.MatrixPolynomial
open scoped BigOperators

def reducedEntry (X : Fin 190 → ℝ) (k : Fin 11) (u v : ℝ) : ℝ :=
  ∑ i : Fin (reducedDim k), ∑ j : Fin (reducedDim k),
    reduced X k i j*feature k (reducedIndex k i) u*feature k (reducedIndex k j) v

theorem matrix_monomial (X : Fin 190 → ℝ) (k : Fin 11) (u v : ℝ) :
    (∑ a : Fin (ambientDim k), ∑ b : Fin (ambientDim k), A X k a b*u^a.val*v^b.val)=reducedEntry X k u v := by
  rw [A,sum_NBN]
  simp only [reducedEntry,ActualKernel.feature_eq_sum,N]

theorem matDot_Y3 (X : Fin 190 → ℝ) (k : Fin 11) (u v t : ℝ) :
    matDot (A X k) (Y3 (ambientDim k) k u v t)=reducedEntry X k u v*Q3 k u v t := by
  rw [← matrix_monomial]
  simp only [matDot,Y3,Matrix.of_apply,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem matDot_S3 (X : Fin 190 → ℝ) (k : Fin 11) (u v t : ℝ) :
    matDot (A X k) (S3 (ambientDim k) k u v t)=(1/6)*
      (reducedEntry X k u v*Q3 k u v t+reducedEntry X k u t*Q3 k u t v+
       reducedEntry X k v u*Q3 k v u t+reducedEntry X k v t*Q3 k v t u+
       reducedEntry X k t u*Q3 k t u v+reducedEntry X k t v*Q3 k t v u) := by
  simp only [S3,ThreePoint.matDot_smul,ThreePoint.matDot_add,matDot_Y3]
end ThomsonNine.ActualF
