import Mathlib.Analysis.Calculus.Deriv.Polynomial
import ThomsonNine.Construction.Moment.FactorModel

-- Isolated source: Moment.Function
noncomputable section
namespace ThomsonNine.CandidateMoment
open ThomsonNine.RationalListPolynomial ThomsonNine.ExactPolynomial Polynomial
open ThomsonNine.CertificateMatrices
open scoped BigOperators

theorem sum_rotate {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (f : α → β → γ → ℝ) :
    (∑ a, ∑ b, ∑ c, f a b c)=∑ c, ∑ a, ∑ b, f a b c := by
  calc
    _ = ∑ a, ∑ c, ∑ b, f a b c := Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

theorem moment_eval (k : Fin 11) (a b : Fin (ambientDim k)) (r : ℝ) :
    (realPolynomial (moment k (ambientIndex k a) (ambientIndex k b))).eval r=
      ∑ pt : Fin 19, (weight pt : ℝ)*
        ThreePoint.S3 (ambientDim k) k (realPoint r pt 0) (realPoint r pt 1) (realPoint r pt 2) a b := by
  rw [moment,ActualKernel.Syzygy.eval_sum,List.map_map,MonomialSymmetry.finRange_sum]
  apply Finset.sum_congr rfl
  intro pt hpt
  simp only [Function.comp_def,scale_sound,eval_mul,eval_C,entry_eq_S3]

theorem block_eval (X : Fin 190 → ℝ) (k : Fin 11) (r : ℝ) :
    (blockPoly X k).eval r=
      ∑ pt : Fin 19, (weight pt : ℝ)*ThreePoint.matDot (A X k)
        (ThreePoint.S3 (ambientDim k) k (realPoint r pt 0) (realPoint r pt 1) (realPoint r pt 2)) := by
  simp only [blockPoly,eval_finsetSum,eval_mul,eval_C,moment_eval,Finset.mul_sum]
  rw [sum_rotate]
  apply Finset.sum_congr rfl
  intro pt hpt
  simp only [ThreePoint.matDot,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

def weightedF (X : Fin 190 → ℝ) (r : ℝ) : ℝ :=
  ∑ pt : Fin 19, (weight pt : ℝ)*ActualF.F X (realPoint r pt 0) (realPoint r pt 1) (realPoint r pt 2)

theorem weightedPoly_eval (X : Fin 190 → ℝ) (r : ℝ) : (weightedPoly X).eval r=weightedF X r := by
  simp only [weightedPoly,eval_finsetSum,block_eval]
  rw [Finset.sum_comm]
  simp only [weightedF,ActualF.F_eq_matrix_pairing,Finset.mul_sum]

theorem weightedF_zero (hf : FactorIdentity) (X : Fin 190 → ℝ) : weightedF X RefinedRadius.radius=0 := by
  rw [← weightedPoly_eval]
  exact weightedPoly_zero hf X

theorem weightedF_stationary (hf : FactorIdentity) (X : Fin 190 → ℝ) :
    HasDerivAt (weightedF X) 0 RefinedRadius.radius := by
  have he : (weightedF X)=(fun r => (weightedPoly X).eval r) := by
    funext r
    exact (weightedPoly_eval X r).symm
  rw [he]
  have h := (weightedPoly X).hasDerivAt RefinedRadius.radius
  rw [weightedPoly_derivative_zero hf X] at h
  exact h
end ThomsonNine.CandidateMoment
