import ThomsonNine.GroupedTranslation

noncomputable section
namespace ThomsonNine.Interval.SparsePolynomial.Collected
open ThomsonNine.Interval.SparsePolynomial.Grouped
open scoped BigOperators

/-- All relative exponents of one translated monomial. -/
def lowerBox (e : Exp3) : Finset Exp3 :=
  ((Finset.range (e 0+1)) ×ˢ
    ((Finset.range (e 1+1)) ×ˢ (Finset.range (e 2+1)))).image
      (fun p => exponentTriple p.1 p.2.1 p.2.2)

 theorem mem_lowerBox (e k : Exp3) : k ∈ lowerBox e ↔ ∀ j, k j ≤ e j := by
  constructor
  · intro hk
    obtain ⟨⟨u,v,t⟩,hp,rfl⟩ := Finset.mem_image.mp hk
    simp only [Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff] at hp
    intro j
    fin_cases j <;> simp [exponentTriple, hp.1, hp.2.1, hp.2.2]
  · intro hk
    apply Finset.mem_image.mpr
    refine ⟨(k 0,k 1,k 2), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff]
      exact ⟨hk 0,hk 1,hk 2⟩
    · funext j
      fin_cases j <;> rfl

 theorem tripleSum_eq_box (e : Exp3) (f : Exp3 → ℝ) :
    tripleSum e f = ∑ k ∈ lowerBox e, f k := by
  unfold lowerBox
  rw [Finset.sum_image]
  · simp only [Finset.sum_product, tripleSum]
  · intro p hp q hq he
    have h0 := congrFun he 0
    have h1 := congrFun he 1
    have h2 := congrFun he 2
    simp only [exponentTriple, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at h0 h1 h2
    exact Prod.ext h0 (Prod.ext h1 h2)

lemma map_filter_sum {α : Type*} (p : α → Prop) [DecidablePred p]
    (v : α → ℝ) (l : List α) :
    ((l.filter (fun i => decide (p i))).map v).sum =
      (l.map (fun i => if p i then v i else 0)).sum := by
  induction l with
  | nil => simp
  | cons i l ih => by_cases h : p i <;> simp [h, ih]

 theorem tripleSum_eq_targets (e : Exp3) (f : Exp3 → ℝ) (q : List Exp3)
    (hq : q.Nodup) (hcover : ∀ k, (∀ j, k j ≤ e j) → k ∈ q) :
    tripleSum e f =
      (q.map (fun k => if ∀ j, k j ≤ e j then f k else 0)).sum := by
  classical
  rw [← map_filter_sum, ← List.sum_toFinset _ (hq.filter _), tripleSum_eq_box]
  congr 1
  ext k
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, mem_lowerBox]
  exact ⟨fun h => ⟨hcover k h,h⟩, fun h => h.2⟩

/-- Finite list sums may be exchanged, retaining repeated source indices. -/
lemma exchange {α β : Type*} (s : List α) (q : List β) (f : α → β → ℝ) :
    (s.map (fun i => (q.map (f i)).sum)).sum =
      (q.map (fun k => (s.map (fun i => f i k)).sum)).sum := by
  induction s with
  | nil => simp
  | cons i s ih => simp [List.sum_map_add, ih]

/-- Collect the full finite binomial expansion into a non-repeating target
support containing every lower exponent of each source. -/
 theorem expandedEval_eq_gathered {α : Type*} (e : α → Exp3) (c : α → ℝ)
    (a x : Fin 3 → ℝ) (s : List α) (q : List Exp3) (hq : q.Nodup)
    (hcover : ∀ i ∈ s, ∀ k, (∀ j, k j ≤ e i j) → k ∈ q) :
    expandedEval e c a x s =
      (q.map (fun k => gatheredOn e k c a s * monomial k x)).sum := by
  have hexp : expandedEval e c a x s =
      (s.map (fun i => tripleSum (e i)
        (fun k => expandedCoefficient (e i) k (c i) a * monomial k x))).sum := by
    clear hcover
    induction s with
    | nil => rfl
    | cons i s ih => simp only [expandedEval, List.map_cons, List.sum_cons, ih]
  rw [hexp]
  trans (s.map (fun i => (q.map (fun k => if ∀ j, k j ≤ e i j then
    expandedCoefficient (e i) k (c i) a * monomial k x else 0)).sum)).sum
  · congr 1
    apply List.map_congr_left
    intro i hi
    exact tripleSum_eq_targets _ _ q hq (hcover i hi)
  rw [exchange]
  congr 1
  apply List.map_congr_left
  intro k hk
  rw [gatheredOn, list_sum_mul]
  simp only [List.map_map, Function.comp_def]
  unfold eligible
  rw [map_filter_sum]

 theorem eval_shift_collected {α : Type*} (e : α → Exp3) (c : α → ℝ)
    (a x : Fin 3 → ℝ) (s : List α) (q : List Exp3) (hq : q.Nodup)
    (hcover : ∀ i ∈ s, ∀ k, (∀ j, k j ≤ e i j) → k ∈ q) :
    eval e c (fun j => a j + x j) s =
      (q.map (fun k => gatheredOn e k c a s * monomial k x)).sum := by
  rw [eval_shift]
  exact expandedEval_eq_gathered e c a x s q hq hcover
end ThomsonNine.Interval.SparsePolynomial.Collected
