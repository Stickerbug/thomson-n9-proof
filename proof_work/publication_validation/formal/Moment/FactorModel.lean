import Moment.Model
import Algebra.MatrixPolynomial
import Kernel.Annihilation
import F.Expansion

noncomputable section
namespace ThomsonNine.CandidateMoment
open ThomsonNine.RationalListPolynomial ThomsonNine.ExactPolynomial Polynomial
open ThomsonNine.CertificateMatrices ThomsonNine.MatrixPolynomial
open scoped BigOperators

def pPoly (k : Fin 11) (a : Fin (ambientDim k)) : ℝ[X] :=
  realPolynomial (ActualKernel.Syzygy.p k (ambientIndex k a))
def cPoly (k : Fin 11) (a : Fin (ambientDim k)) : ℝ[X] :=
  realPolynomial (ActualKernel.Syzygy.c k (ambientIndex k a))
def oddPoly (k : Fin 11) : ℝ[X] := realPolynomial (if k.val%2=0 then [1] else [1,0,-1])
def blockPoly (X : Fin 190 → ℝ) (k : Fin 11) : ℝ[X] :=
  ∑ a : Fin (ambientDim k), ∑ b : Fin (ambientDim k),
    C (A X k a b)*realPolynomial (moment k (ambientIndex k a) (ambientIndex k b))
def weightedPoly (X : Fin 190 → ℝ) : ℝ[X] := ∑ k : Fin 11, blockPoly X k

def FactorIdentity : Prop := ∀ (k : Fin 11) (a b : Fin (ambientDim k)),
  realPolynomial (moment k (ambientIndex k a) (ambientIndex k b))=
    realPolynomial (factor k (ambientIndex k a) (ambientIndex k b))

theorem factor_polynomial (k : Fin 11) (a b : Fin (ambientDim k)) :
    realPolynomial (factor k (ambientIndex k a) (ambientIndex k b)) =
      oddPoly k*pPoly k a*pPoly k b+C (1/2)*cPoly k a*cPoly k b := by
  simp only [factor,add_sound,mul_sound,scale_sound,pPoly,cPoly,oddPoly]
  norm_num only [Rat.cast_div,Rat.cast_ofNat]
  ring

theorem block_factor (hf : FactorIdentity) (X : Fin 190 → ℝ) (k : Fin 11) :
    blockPoly X k=oddPoly k*bilinear (A X k) (pPoly k) (pPoly k)+
      C (1/2)*bilinear (A X k) (cPoly k) (cPoly k) := by
  simp only [blockPoly,bilinear,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [hf k a b,factor_polynomial]
  ring

theorem A_symmetric (X : Fin 190 → ℝ) (k : Fin 11) (a b : Fin (ambientDim k)) :
    A X k a b=A X k b a := by
  have hb : (reduced X k).transpose=reduced X k := by
    ext i j
    exact reduced_symmetric X k j i
  have ha : (A X k).transpose=A X k := by
    simp only [A,Matrix.transpose_mul,Matrix.transpose_transpose,hb,Matrix.mul_assoc]
  exact (congrArg (fun M => M a b) ha).symm

theorem p_quadratic_zero (X : Fin 190 → ℝ) (k : Fin 11) :
    (bilinear (A X k) (pPoly k) (pPoly k)).eval RefinedRadius.radius=0 :=
  quadratic_zero _ _ _ (ActualKernel.Syzygy.A_p_zero X k)
theorem c_quadratic_zero (X : Fin 190 → ℝ) (k : Fin 11) :
    (bilinear (A X k) (cPoly k) (cPoly k)).eval RefinedRadius.radius=0 :=
  quadratic_zero _ _ _ (ActualKernel.Syzygy.A_c_zero X k)
theorem p_quadratic_derivative_zero (X : Fin 190 → ℝ) (k : Fin 11) :
    (bilinear (A X k) (pPoly k) (pPoly k)).derivative.eval RefinedRadius.radius=0 :=
  quadratic_derivative_zero _ (A_symmetric X k) _ _ (ActualKernel.Syzygy.A_p_zero X k)
theorem c_quadratic_derivative_zero (X : Fin 190 → ℝ) (k : Fin 11) :
    (bilinear (A X k) (cPoly k) (cPoly k)).derivative.eval RefinedRadius.radius=0 :=
  quadratic_derivative_zero _ (A_symmetric X k) _ _ (ActualKernel.Syzygy.A_c_zero X k)

theorem weightedPoly_zero (hf : FactorIdentity) (X : Fin 190 → ℝ) :
    (weightedPoly X).eval RefinedRadius.radius=0 := by
  simp only [weightedPoly,eval_finsetSum]
  apply Finset.sum_eq_zero
  intro k hk
  rw [block_factor hf,eval_add,eval_mul,eval_mul,p_quadratic_zero,c_quadratic_zero]
  ring

theorem weightedPoly_derivative_zero (hf : FactorIdentity) (X : Fin 190 → ℝ) :
    (weightedPoly X).derivative.eval RefinedRadius.radius=0 := by
  simp only [weightedPoly,derivative_sum,eval_finsetSum]
  apply Finset.sum_eq_zero
  intro k hk
  rw [block_factor hf]
  simp only [derivative_add,derivative_mul,derivative_C,eval_add,eval_mul,eval_zero,
    p_quadratic_zero,p_quadratic_derivative_zero,c_quadratic_zero,c_quadratic_derivative_zero]
  ring
end ThomsonNine.CandidateMoment
