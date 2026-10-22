import ThomsonNine.Construction.Moment.QStep00
import ThomsonNine.Construction.Moment.QStep01
import ThomsonNine.Construction.Moment.QStep02
import ThomsonNine.Construction.Moment.QStep03
import ThomsonNine.Construction.Moment.QStep04
import ThomsonNine.Construction.Moment.QStep05
import ThomsonNine.Construction.Moment.QStep06
import ThomsonNine.Construction.Moment.QStep07
import ThomsonNine.Construction.Moment.QStep08
import ThomsonNine.Construction.Moment.QStep09
import ThomsonNine.Construction.Moment.QStep10
import ThomsonNine.Construction.Moment.QStep11
import ThomsonNine.Construction.Moment.QStep12
import ThomsonNine.Construction.Moment.QStep13
import ThomsonNine.Construction.Moment.QStep14
import ThomsonNine.Construction.Moment.QStep15
import ThomsonNine.Construction.Moment.QStep16
import ThomsonNine.Construction.Moment.QStep17
import ThomsonNine.Construction.Moment.QStep18
import ThomsonNine.Construction.Kernel.Syzygy
import ThomsonNine.Construction.Matrices.Model

-- Isolated source: Moment.Model
set_option maxRecDepth 100000
noncomputable section
namespace ThomsonNine.CandidateMoment
open ThomsonNine.ExactPolynomial ThomsonNine.RationalListPolynomial Polynomial
open scoped BigOperators
theorem q_step (pt : Fin 19) : qStepValid pt := by
  fin_cases pt
  · exact q_step_00
  · exact q_step_01
  · exact q_step_02
  · exact q_step_03
  · exact q_step_04
  · exact q_step_05
  · exact q_step_06
  · exact q_step_07
  · exact q_step_08
  · exact q_step_09
  · exact q_step_10
  · exact q_step_11
  · exact q_step_12
  · exact q_step_13
  · exact q_step_14
  · exact q_step_15
  · exact q_step_16
  · exact q_step_17
  · exact q_step_18

theorem q_cache_eq (pt : Fin 19) (σ : Fin 6) (n : ℕ) (hn : n<11) :
    qCache pt σ ⟨n,hn⟩=q (permuted pt σ 0) (permuted pt σ 1) (permuted pt σ 2) n := by
  induction n using Nat.twoStepInduction with
  | zero => exact q_zero pt σ
  | one => exact q_one pt σ
  | more n ih ih' =>
    rw [q_step pt σ ⟨n,by omega⟩,ih (by omega),ih' (by omega)]
    rfl

def realNodes (r : ℝ) (j : Fin 7) : ℝ := (realPolynomial (nodes j)).eval r
def realPoint (r : ℝ) (pt : Fin 19) (j : Fin 3) : ℝ := realNodes r (points pt j)

theorem q_cache_eval (pt : Fin 19) (σ : Fin 6) (k : Fin 11) (r : ℝ) :
    (realPolynomial (qCache pt σ k)).eval r =
      ThreePoint.Q3 k (realPoint r pt (ActualKernel.QCache.permutation σ 0))
        (realPoint r pt (ActualKernel.QCache.permutation σ 1))
        (realPoint r pt (ActualKernel.QCache.permutation σ 2)) := by
  rw [q_cache_eq pt σ k.val k.isLt,q_eval]
  rfl

theorem power_cache_eval (j : Fin 7) (a : Fin 11) (r : ℝ) :
    (realPolynomial (powerCache j a)).eval r=(realNodes r j)^a.val := by
  rw [powers_valid,pow_sound,eval_pow]
  rfl

theorem entry_eval (k a b : Fin 11) (pt : Fin 19) (r : ℝ) :
    (realPolynomial (entry k a b pt)).eval r = (1/6)*
      ∑ σ : Fin 6,
        (realPoint r pt (ActualKernel.QCache.permutation σ 0))^a.val*
        (realPoint r pt (ActualKernel.QCache.permutation σ 1))^b.val*
        ThreePoint.Q3 k (realPoint r pt (ActualKernel.QCache.permutation σ 0))
          (realPoint r pt (ActualKernel.QCache.permutation σ 1))
          (realPoint r pt (ActualKernel.QCache.permutation σ 2)) := by
  simp only [entry,scale_sound,eval_mul,eval_C,ActualKernel.Syzygy.eval_sum,List.map_map,Function.comp_def]
  rw [MonomialSymmetry.finRange_sum]
  norm_num only [Rat.cast_div,Rat.cast_ofNat]
  congr 1
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [mul_sound,mul_sound,eval_mul,eval_mul,power_cache_eval,power_cache_eval,q_cache_eval]
  rfl

theorem entry_eq_S3 (k : Fin 11) (a b : Fin (CertificateMatrices.ambientDim k)) (pt : Fin 19) (r : ℝ) :
    (realPolynomial (entry k (CertificateMatrices.ambientIndex k a) (CertificateMatrices.ambientIndex k b) pt)).eval r =
      ThreePoint.S3 (CertificateMatrices.ambientDim k) k
        (realPoint r pt 0) (realPoint r pt 1) (realPoint r pt 2) a b := by
  rw [entry_eval]
  simp [Fin.sum_univ_succ,ActualKernel.QCache.permutation,ThreePoint.S3,ThreePoint.Y3,CertificateMatrices.ambientIndex]
  ring
end ThomsonNine.CandidateMoment
