import ThomsonNine.AAASupport
import ThomsonNine.CoordinateTranslation
import ThomsonNine.AAAFixedComplete

set_option maxRecDepth 100000
noncomputable section
namespace ThomsonNine.AAACollected
open ThomsonNine.Interval ThomsonNine.Interval.RatInterval
open ThomsonNine.Interval.SparsePolynomial ThomsonNine.Interval.SparsePolynomial.Grouped
open ThomsonNine.Interval.SparsePolynomial.Collected
open ThomsonNine.LocalSparseHessianAAA ThomsonNine.GatheredBinding
open ThomsonNine.AAAGroupedData ThomsonNine.AAASupport

lemma eval_eq_map_sum {α : Type*} (e : α → Exp3) (c : α → ℝ)
    (x : Fin 3 → ℝ) (l : List α) :
    eval e c x l = (l.map (fun i => c i * monomial (e i) x)).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => simpa only [eval, List.map_cons, List.sum_cons] using congrArg (fun z => c i * monomial (e i) x + z) ih

/-- Full gathered coefficients describe exactly the fixed source polynomial
translated by one fixed center. This is an equality of real polynomial values. -/
theorem eval_shift_gathered (c : TermIndex → ℝ) (a x : Fin 3 → ℝ) :
    eval exponents c (fun j => a j+x j) allTerms =
      eval exponents (fun k => gathered (exponents k) c a) x allTerms := by
  have hcover : ∀ i ∈ allTerms, ∀ k : Exp3, (∀ j, k j ≤ exponents i j) → k ∈ support := by
    intro i hi k hk
    apply support_lower_closed (exponents i) _ k hk
    rw [support_eq]
    exact List.mem_map.mpr ⟨i,hi,rfl⟩
  rw [eval_shift_collected exponents c a x allTerms support support_nodup hcover]
  rw [support_eq, eval_eq_map_sum]
  simp only [List.map_map, Function.comp_def]
  rfl

 theorem terms_eq_allTerms : terms = allTerms := by rfl

/-- The existing interval certificate now bounds the actual second derivative
of the original fixed source polynomial at a+x, rather than only a separately
supplied coefficient family. Source/center memberships are still premises. -/
theorem source_h00_mem (c : TermIndex → ℝ) (a x : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i))
    (hx : ∀ i, (relativeBox i).mem (x i)) :
    targetH00.mem
      (axisDeriv (axisDeriv (fun y => eval exponents c y allTerms) 0) 0
        (fun i => a i+x i)) := by
  have h := AAAFixedComplete.gathered_h00_mem c a x hC ha hx
  rw [terms_eq_allTerms] at h
  have hfun : translate a (fun y => eval exponents c y allTerms) =
      fun y => eval exponents (fun k => gathered (exponents k) c a) y allTerms := by
    funext y
    exact eval_shift_gathered c a y
  rw [← hfun, axisDeriv_axisDeriv_translate] at h
  exact h
end ThomsonNine.AAACollected
