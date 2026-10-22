import ThomsonNine.IntervalListPolynomial
import Mathlib.Data.List.Sort

-- Isolated source: Algebra.FiniteCollector
noncomputable section
namespace ThomsonNine.FiniteCollector

def mergeFuel : ℕ → List ℕ → List ℕ → List ℕ
  | 0,xs,ys => xs++ys
  | _+1,[],ys => ys
  | _+1,xs,[] => xs
  | n+1,x::xs,y::ys =>
    if x≤y then x::mergeFuel n xs (y::ys) else y::mergeFuel n (x::xs) ys
theorem mergeFuel_perm (n : ℕ) (xs ys : List ℕ) : (mergeFuel n xs ys).Perm (xs++ys) := by
  induction n generalizing xs ys with
  | zero => exact List.Perm.refl _
  | succ n ih =>
    cases xs with
    | nil => simp [mergeFuel]
    | cons x xs =>
      cases ys with
      | nil => simp [mergeFuel]
      | cons y ys =>
        simp only [mergeFuel]
        split_ifs
        · exact (ih xs (y::ys)).cons x
        · exact ((ih (x::xs) ys).cons y).trans List.perm_middle.symm
def sortFuel : ℕ → List ℕ → List ℕ
  | 0,l => l
  | n+1,l =>
    if l.length≤1 then l else
      let a := sortFuel n (l.take (l.length/2))
      let b := sortFuel n (l.drop (l.length/2))
      mergeFuel (a.length+b.length) a b
theorem sortFuel_perm (n : ℕ) (l : List ℕ) : (sortFuel n l).Perm l := by
  induction n generalizing l with
  | zero => exact List.Perm.refl _
  | succ n ih =>
    rw [sortFuel]
    split_ifs
    · exact List.Perm.refl _
    · exact (mergeFuel_perm _ _ _).trans
        (((ih (l.take (l.length/2))).append (ih (l.drop (l.length/2)))).trans
          (by rw [List.take_append_drop]))
theorem partition_of_fuel_sorted {l : List ℕ} {n fuel : ℕ}
    (h : sortFuel fuel l=List.range n) : l.Perm (List.range n) :=
  (sortFuel_perm fuel l).symm.trans (List.Perm.of_eq h)

theorem partition_of_sorted {l : List ℕ} {n : ℕ}
    (h : l.mergeSort (·≤·)=List.range n) : l.Perm (List.range n) := by
  rw [← h]
  exact (List.mergeSort_perm l (·≤·)).symm

theorem weighted_list (l : List ℕ) (c : ℕ → ℝ) (m : ℝ) :
    (l.map c).sum*m=(l.map (fun i => c i*m)).sum := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih,add_mul]

theorem flatMap_sum {α : Type*} (targets : List α) (groups : α → List ℕ) (c : ℕ → ℝ) :
    (targets.map (fun j => ((groups j).map c).sum)).sum=((targets.flatMap groups).map c).sum := by
  induction targets with
  | nil => simp
  | cons j js ih => simp [ih]

theorem collected_eval {α : Type*} (targets : List α) (groups : α → List ℕ)
    (n : ℕ) (c sm : ℕ → ℝ) (tm : α → ℝ)
    (hp : (targets.flatMap groups).Perm (List.range n))
    (hm : ∀ j ∈ targets, ∀ i ∈ groups j, sm i=tm j) :
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
    rw [hm j hj i hi]
  rw [he,flatMap_sum]
  exact (hp.map (fun i => c i*sm i)).sum_eq
end ThomsonNine.FiniteCollector
