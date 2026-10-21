/-
Finite-sum enclosure for the certificate evaluator.

`sumIntervals` folds interval addition over a finite list, and `mem_sumIntervals`
proves that the result encloses the sum of any real values enclosed by the
corresponding list entries.  This is the last bookkeeping step before the
whole-tensor evaluator `evalTensor`.
-/
import ThomsonNine.IntervalEval

namespace ThomsonNine
namespace Interval
namespace RatInterval

/-- Fold interval addition over a list, starting from zero. -/
def sumIntervals : List RatInterval → RatInterval
  | [] => const 0
  | I :: Is => add I (sumIntervals Is)

/-- Soundness of `sumIntervals` for lists of interval/value pairs. -/
theorem mem_sumIntervals : ∀ (l : List (RatInterval × ℝ)),
    (∀ p ∈ l, p.1.mem p.2) → (sumIntervals (l.map Prod.fst)).mem (l.map Prod.snd).sum
  | [], _ => by
      show (const 0).mem (0 : ℝ)
      simpa using (mem_const (0 : ℚ))
  | p :: ps, h => by
      have hp : p.1.mem p.2 := h p (by simp)
      have hps : ∀ q ∈ ps, q.1.mem q.2 := fun q hq => h q (by simp [hq])
      have ih := mem_sumIntervals ps hps
      simp only [List.map_cons, List.sum_cons, sumIntervals]
      exact mem_add hp ih

end RatInterval
end Interval
end ThomsonNine
