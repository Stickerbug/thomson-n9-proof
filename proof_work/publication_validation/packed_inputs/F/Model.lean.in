import F.BaseModel
import F.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualF
open ThomsonNine.ActualF.Data
open ThomsonNine.CertificateMatrices
open ThomsonNine.ActualHermite.CoefficientData
open ThomsonNine.FixedInterval
open scoped BigOperators
theorem eval_eq_raw (X : Fin 190 → ℝ) (u v t : ℝ) : F X u v t=rawEval X u v t := by
  have h := FiniteCollector.collected_eval (List.finRange 756) groups count
    (fun n => sourceCoefficient X (decode n))
    (fun n => QPolynomial.monomial (exponent (decode n)) u v t)
    (fun j => QPolynomial.monomial (support j) u v t)
    groups_partition (fun j _ n hn => by rw [group_exponent j n hn])
  have hs : ((List.finRange 756).map (fun j =>
      ((groups j).map (fun n => sourceCoefficient X (decode n))).sum*
        QPolynomial.monomial (support j) u v t)).sum =
      ∑ j : Fin 756, ((groups j).map (fun n => sourceCoefficient X (decode n))).sum*
        QPolynomial.monomial (support j) u v t := by
    symm
    have hh := List.sum_toFinset (fun j : Fin 756 =>
      ((groups j).map (fun n => sourceCoefficient X (decode n))).sum*QPolynomial.monomial (support j) u v t)
      (show (List.finRange 756).Nodup by exact List.nodup_finRange _)
    have he : (List.finRange 756).toFinset=(Finset.univ : Finset (Fin 756)) := by ext i; simp
    simpa only [he] using hh
  rw [hs] at h
  unfold F rawEval coefficient
  rw [← h,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring
end ThomsonNine.ActualF
