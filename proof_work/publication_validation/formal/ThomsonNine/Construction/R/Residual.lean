import ThomsonNine.Construction.R.Collected
import ThomsonNine.Construction.R.Operators
import ThomsonNine.Construction.R.Bounds

-- Isolated source: R.Residual
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
noncomputable section
namespace ThomsonNine.ActualR
open ThomsonNine.LocalSparseHessianAAA
open ThomsonNine.Interval.SparsePolynomial

theorem polynomial_eq_residual (u v t : ℝ) :
    polynomial u v t =
      ActualHermite.H.eval u+ActualHermite.H.eval v+ActualHermite.H.eval t-
        7*ActualF.F X u v t-
        ActualF.F X 1 u u-ActualF.F X 1 v v-ActualF.F X 1 t t-ActualF.Constants.c X := by
  rw [polynomial_eq_raw]
  exact Collection.rawOperatorEval_eq_residual u v t

theorem allTerms_sourceIndex : GatheredBinding.allTerms.map Data.sourceIndex=List.finRange 807 := by decide +kernel
theorem source_eval_eq_polynomial (x : Fin 3 → ℝ) :
    eval exponents family x GatheredBinding.allTerms=polynomial (x 0) (x 1) (x 2) := by
  rw [AAACollected.eval_eq_map_sum]
  have hm : (GatheredBinding.allTerms.map (fun t => family t*monomial (exponents t) x)) =
      (GatheredBinding.allTerms.map Data.sourceIndex).map
        (fun j => coefficient j*monomial (Data.sourceExponent j) x) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro t ht
    simp only [Function.comp_def,family,Data.sourceExponent,Data.termIndex_sourceIndex]
  rw [hm,allTerms_sourceIndex,MonomialSymmetry.finRange_sum]
  rfl

def residual (x : Fin 3 → ℝ) : ℝ :=
  ActualHermite.H.eval (x 0)+ActualHermite.H.eval (x 1)+ActualHermite.H.eval (x 2)-
    7*ActualF.F X (x 0) (x 1) (x 2)-
    ActualF.F X 1 (x 0) (x 0)-ActualF.F X 1 (x 1) (x 1)-ActualF.F X 1 (x 2) (x 2)-ActualF.Constants.c X
theorem source_function_eq :
    (fun y => eval exponents family y GatheredBinding.allTerms)=residual := by
  funext y
  rw [source_eval_eq_polynomial,polynomial_eq_residual]
  rfl
theorem actual_source_h00_mem (x : Fin 3 → ℝ) (hx : ∀ i, (relativeBox i).mem (x i)) :
    targetH00.mem
      (axisDeriv (axisDeriv residual 0) 0 (fun i => RefinedRadius.aaaCenter i+x i)) := by
  have h := RefinedRadius.source_h00_at_actual_center family x Certified.family_mem hx
  rw [source_function_eq] at h
  exact h
end ThomsonNine.ActualR
