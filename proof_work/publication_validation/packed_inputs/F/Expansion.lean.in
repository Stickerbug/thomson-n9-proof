import F.Model
import Algebra.MonomialSymmetry

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
noncomputable section
namespace ThomsonNine.ActualF
open ThomsonNine.ActualF.Data
open ThomsonNine.CertificateMatrices
open ThomsonNine.MonomialSymmetry
open scoped BigOperators

def sourceEval (X : Fin 190 → ℝ) (u v t : ℝ) (s : Source) : ℝ :=
  sourceCoefficient X s*QPolynomial.monomial (exponent s) u v t
theorem rawEval_eq_allSources (X : Fin 190 → ℝ) (u v t : ℝ) :
    rawEval X u v t=(1/6)*(allSources.map (sourceEval X u v t)).sum := by
  have h := congrArg (fun l : List Source => (1/6)*(l.map (sourceEval X u v t)).sum) decoded_range
  simpa only [rawEval,sourceEval,List.map_map,Function.comp_def] using h

theorem source_monomial (s : Source) (u v t : ℝ) :
    QPolynomial.monomial (exponent s) u v t =
      (![u,v,t] (ActualKernel.QCache.permutation s.permutation 0))^s.left*
      (![u,v,t] (ActualKernel.QCache.permutation s.permutation 1))^s.right*
        QPolynomial.monomial (Data.term s).1
          (![u,v,t] (ActualKernel.QCache.permutation s.permutation 0))
          (![u,v,t] (ActualKernel.QCache.permutation s.permutation 1))
          (![u,v,t] (ActualKernel.QCache.permutation s.permutation 2)) := by
  exact shifted_monomial (Data.term s).1 s.left s.right s.permutation u v t

theorem term_sum (X : Fin 190 → ℝ) (k : Fin 11) (a b : Fin (ambientDim k)) (σ : Fin 6) (u v t : ℝ) :
    ((List.finRange (termCount k)).map (fun q => sourceEval X u v t ⟨k,a.val,b.val,σ,q.val⟩)).sum =
      A X k a b*(![u,v,t] (ActualKernel.QCache.permutation σ 0))^a.val*
        (![u,v,t] (ActualKernel.QCache.permutation σ 1))^b.val*
        ThreePoint.Q3 k
          (![u,v,t] (ActualKernel.QCache.permutation σ 0))
          (![u,v,t] (ActualKernel.QCache.permutation σ 1))
          (![u,v,t] (ActualKernel.QCache.permutation σ 2)) := by
  let U := ![u,v,t] (ActualKernel.QCache.permutation σ 0)
  let V := ![u,v,t] (ActualKernel.QCache.permutation σ 1)
  let T := ![u,v,t] (ActualKernel.QCache.permutation σ 2)
  have he (q : Fin (termCount k)) :
      sourceEval X u v t ⟨k,a.val,b.val,σ,q.val⟩ =
        (A X k a b*U^a.val*V^b.val)*
          (((((QPolynomial.terms k)[q.val]?).getD (![0,0,0],0)).2 : ℝ)*
            QPolynomial.monomial (((QPolynomial.terms k)[q.val]?).getD (![0,0,0],0)).1 U V T) := by
    have hl : leftIndex ⟨k,a.val,b.val,σ,q.val⟩=a := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt a.isLt
    have hr : rightIndex ⟨k,a.val,b.val,σ,q.val⟩=b := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt b.isLt
    rw [sourceEval,sourceCoefficient,hl,hr,source_monomial]
    change (((((QPolynomial.terms k)[q.val]?).getD (![0,0,0],0)).2 : ℝ)*A X k a b)*
      (U^a.val*V^b.val*QPolynomial.monomial (((QPolynomial.terms k)[q.val]?).getD (![0,0,0],0)).1 U V T) = _
    ring
  have hm := List.map_congr_left (fun q (_ : q∈List.finRange (termCount k)) => he q)
  rw [hm,map_mul_sum]
  have hq := list_indexed_sum (QPolynomial.terms k) (![0,0,0],(0 : ℤ))
    (fun q => (q.2 : ℝ)*QPolynomial.monomial q.1 U V T)
  dsimp only [Data.termCount]
  rw [hq]
  change (A X k a b*U^a.val*V^b.val)*QPolynomial.eval k U V T = _
  rw [QPolynomial.eval_eq_Q3]

theorem allSources_sum (X : Fin 190 → ℝ) (u v t : ℝ) :
    (allSources.map (sourceEval X u v t)).sum =
      ∑ k : Fin 11, ∑ a : Fin (ambientDim k), ∑ b : Fin (ambientDim k), ∑ σ : Fin 6,
        A X k a b*(![u,v,t] (ActualKernel.QCache.permutation σ 0))^a.val*
          (![u,v,t] (ActualKernel.QCache.permutation σ 1))^b.val*
          ThreePoint.Q3 k
            (![u,v,t] (ActualKernel.QCache.permutation σ 0))
            (![u,v,t] (ActualKernel.QCache.permutation σ 1))
            (![u,v,t] (ActualKernel.QCache.permutation σ 2)) := by
  rw [allSources,flatMap_sum_map,finRange_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [blockSources,flatMap_sum_map,finRange_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [flatMap_sum_map,finRange_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [flatMap_sum_map,finRange_sum]
  exact Finset.sum_congr rfl (fun σ _ => by
    simpa only [List.map_map,Function.comp_def] using term_sum X k a b σ u v t)

theorem symmetrized_entry (m k : ℕ) (B : Matrix (Fin m) (Fin m) ℝ) (a b : Fin m) (u v t : ℝ) :
    (1/6)*(∑ σ : Fin 6, B a b*(![u,v,t] (ActualKernel.QCache.permutation σ 0))^a.val*
      (![u,v,t] (ActualKernel.QCache.permutation σ 1))^b.val*
      ThreePoint.Q3 k
        (![u,v,t] (ActualKernel.QCache.permutation σ 0))
        (![u,v,t] (ActualKernel.QCache.permutation σ 1))
        (![u,v,t] (ActualKernel.QCache.permutation σ 2))) =
      B a b*(ThreePoint.S3 m k u v t) a b := by
  simp [Fin.sum_univ_succ,ActualKernel.QCache.permutation,ThreePoint.S3,ThreePoint.Y3]
  ring

theorem F_eq_matrix_pairing (X : Fin 190 → ℝ) (u v t : ℝ) :
    F X u v t=∑ k : Fin 11, ThreePoint.matDot (A X k) (ThreePoint.S3 (ambientDim k) k u v t) := by
  rw [eval_eq_raw,rawEval_eq_allSources,allSources_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  change (1/6)*(∑ a : Fin (ambientDim k), ∑ b : Fin (ambientDim k), ∑ σ : Fin 6, _) =
    ∑ a : Fin (ambientDim k), ∑ b : Fin (ambientDim k), _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun b _ => symmetrized_entry (ambientDim k) k (A X k) a b u v t)
end ThomsonNine.ActualF
