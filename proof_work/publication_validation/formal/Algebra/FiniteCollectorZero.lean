import Algebra.FiniteCollector

noncomputable section
namespace ThomsonNine.FiniteCollector

theorem collected_eval_zero {α : Type*} (targets : List α) (groups : α → List ℕ)
    (n : ℕ) (c sm : ℕ → ℝ) (tm : α → ℝ)
    (hp : (targets.flatMap groups).Perm (List.range n))
    (hm : ∀ j ∈ targets, ∀ i ∈ groups j, c i=0 ∨ sm i=tm j) :
    (targets.map (fun j => ((groups j).map c).sum*tm j)).sum=
      ((List.range n).map (fun i => c i*sm i)).sum := by
  have he : (targets.map (fun j => ((groups j).map c).sum*tm j)).sum=
      (targets.map (fun j => ((groups j).map (fun i => c i*sm i)).sum)).sum := by
    congr 1
    apply List.map_congr_left
    intro j hj
    rw [weighted_list]
    congr 1
    apply List.map_congr_left
    intro i hi
    rcases hm j hj i hi with hz|he
    · simp [hz]
    · rw [he]
  rw [he,flatMap_sum]
  exact (hp.map (fun i => c i*sm i)).sum_eq
end ThomsonNine.FiniteCollector
