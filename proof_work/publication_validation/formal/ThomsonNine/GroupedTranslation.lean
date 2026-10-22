import ThomsonNine.SparseTranslation

noncomputable section
namespace ThomsonNine.Interval.SparsePolynomial.Grouped
open ThomsonNine.Interval ThomsonNine.Interval.RatInterval
open scoped BigOperators

variable {ι κ : Type*} [DecidableEq κ]

def keys (f : ι → κ) (s : List ι) : List κ := (s.map f).dedup

def fiber (f : ι → κ) (v : ι → ℝ) (s : List ι) (k : κ) : ℝ :=
  ((s.filter (fun i => f i == k)).map v).sum

lemma sum_filter_eq (f : ι → κ) (v : ι → ℝ) (s : List ι) (k : κ) :
    fiber f v s k = (s.map (fun i => if f i = k then v i else 0)).sum := by
  induction s with
  | nil => simp [fiber]
  | cons i s ih =>
    by_cases h : f i = k <;> simp [fiber, h] at ih ⊢ <;> exact ih

omit [DecidableEq κ] in
lemma exchange (G : Finset κ) (s : List ι) (v : κ → ι → ℝ) :
    (∑ g ∈ G, (s.map (v g)).sum) = (s.map (fun i => ∑ g ∈ G, v g i)).sum := by
  induction s with
  | nil => simp
  | cons i s ih => simp [Finset.sum_add_distrib, ih]

lemma list_sum_mul (l : List ℝ) (a : ℝ) : l.sum * a = (l.map (fun x => x * a)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [add_mul, ih]

lemma regroup_finset (G : Finset κ) (f : ι → κ) (s : List ι)
    (v : ι → ℝ) (w : κ → ℝ) (h : ∀ i ∈ s, f i ∈ G) :
    (∑ g ∈ G, fiber f v s g * w g) = (s.map (fun i => v i * w (f i))).sum := by
  calc
    _ = ∑ g ∈ G, (s.map (fun i => if f i = g then v i * w g else 0)).sum := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [sum_filter_eq, list_sum_mul]
      congr 1
      simp only [List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro i hi
      split <;> simp_all
    _ = (s.map (fun i => ∑ g ∈ G, if f i = g then v i * w g else 0)).sum := exchange G s _
    _ = _ := by
      congr 1
      apply List.map_congr_left
      intro i hi
      simp [h i hi]

theorem regroup (f : ι → κ) (s : List ι) (v : ι → ℝ) (w : κ → ℝ) :
    ((keys f s).map (fun g => fiber f v s g * w g)).sum =
      (s.map (fun i => v i * w (f i))).sum := by
  change ((s.map f).dedup.map (fun g => fiber f v s g * w g)).sum = _
  rw [← List.sum_toFinset _ (List.nodup_dedup (s.map f))]
  apply regroup_finset
  intro i hi
  simp only [List.mem_toFinset, List.mem_dedup, List.mem_map]
  exact ⟨i, hi, rfl⟩

/-- Sources contributing to one target in the full binomial expansion. -/
def eligible {α : Type*} (e : α → Exp3) (k : Exp3) (s : List α) : List α :=
  s.filter (fun i => decide (∀ j, k j ≤ e i j))

/-- Full gathered coefficient, retaining repeated source indices. -/
def gatheredOn {α : Type*} (e : α → Exp3) (k : Exp3)
    (c : α → ℝ) (a : Fin 3 → ℝ) (s : List α) : ℝ :=
  ((eligible e k s).map (fun i => expandedCoefficient (e i) k (c i) a)).sum

/-- Group axis-0 contributions by the remaining pair, then by axis 2. -/
def groupedCoeff {α : Type*} (e : α → Exp3) (k : Exp3)
    (c : α → ℝ) (a : Fin 3 → ℝ) (s : List α) : ℝ :=
  let S := eligible e k s
  let f := fun i => (e i 1, e i 2)
  let G := keys f S
  let v₀ := fun i => c i * shiftFactor (e i 0) (k 0) (a 0)
  let v₁ := fun g : ℕ × ℕ => fiber f v₀ S g * shiftFactor g.1 (k 1) (a 1)
  ((keys Prod.snd G).map (fun h => fiber Prod.snd v₁ G h *
    shiftFactor h (k 2) (a 2))).sum

/-- Universal algebraic bridge: grouping is exactly the full gathered sum.
No source-count bound, distinctness, sign or interval assumptions are needed. -/
theorem groupedCoeff_eq_gatheredOn {α : Type*} (e : α → Exp3) (k : Exp3)
    (c : α → ℝ) (a : Fin 3 → ℝ) (s : List α) :
    groupedCoeff e k c a s = gatheredOn e k c a s := by
  dsimp only [groupedCoeff]
  rw [regroup]
  simp only [mul_assoc]
  rw [regroup]
  simp only [gatheredOn, expandedCoefficient, mul_assoc]

/-- Interval sum of a fixed finite family. -/
def fiberInterval {α β : Type*} [DecidableEq β] (f : α → β)
    (C : α → RatInterval) (s : List α) (k : β) : RatInterval :=
  sumIntervals ((s.filter (fun i => f i == k)).map C)

lemma mapped_sum_mem {α : Type*} (C : α → RatInterval) (c : α → ℝ) (s : List α)
    (h : ∀ i ∈ s, (C i).mem (c i)) :
    (sumIntervals (s.map C)).mem (s.map c).sum := by
  induction s with
  | nil => simpa [sumIntervals] using mem_const (0 : ℚ)
  | cons i s ih =>
    exact mem_add (h i (by simp)) (ih (fun j hj => h j (by simp [hj])))

lemma fiber_mem {α β : Type*} [DecidableEq β] (f : α → β)
    (C : α → RatInterval) (c : α → ℝ) (s : List α) (k : β)
    (h : ∀ i ∈ s, (C i).mem (c i)) :
    (fiberInterval f C s k).mem (fiber f c s k) := by
  exact mapped_sum_mem C c _ (fun i hi => h i (List.mem_filter.mp hi).1)

/-- Computable interval counterpart of the two keyed grouping stages. -/
def groupedInterval {α : Type*} (e : α → Exp3) (k : Exp3)
    (C : α → RatInterval) (P : Fin 3 → ℕ → RatInterval) (s : List α) : RatInterval :=
  let S := eligible e k s
  let f := fun i => (e i 1, e i 2)
  let G := keys f S
  let C₀ := fun i => mul (C i) (shiftFactorInterval (e i 0) (k 0) (P 0))
  let C₁ := fun g : ℕ × ℕ => mul (fiberInterval f C₀ S g)
    (shiftFactorInterval g.1 (k 1) (P 1))
  sumIntervals ((keys Prod.snd G).map (fun h =>
    mul (fiberInterval Prod.snd C₁ G h) (shiftFactorInterval h (k 2) (P 2))))

/-- All targets at once: one proof of the algorithm encloses the full gathered
coefficient of any fixed finite source family, with arbitrary signs or repeats. -/
theorem groupedInterval_mem {α : Type*} (e : α → Exp3) (k : Exp3)
    (C : α → RatInterval) (c : α → ℝ) (P : Fin 3 → ℕ → RatInterval)
    (a : Fin 3 → ℝ) (s : List α)
    (hC : ∀ i ∈ s, (C i).mem (c i)) (hP : PowerEnclosures P a) :
    (groupedInterval e k C P s).mem (gatheredOn e k c a s) := by
  let S := eligible e k s
  let f := fun i => (e i 1, e i 2)
  let G := keys f S
  let C₀ := fun i => mul (C i) (shiftFactorInterval (e i 0) (k 0) (P 0))
  let c₀ := fun i => c i * shiftFactor (e i 0) (k 0) (a 0)
  let C₁ := fun g : ℕ × ℕ => mul (fiberInterval f C₀ S g)
    (shiftFactorInterval g.1 (k 1) (P 1))
  let c₁ := fun g : ℕ × ℕ => fiber f c₀ S g * shiftFactor g.1 (k 1) (a 1)
  have h₀ : ∀ i ∈ S, (C₀ i).mem (c₀ i) := by
    intro i hi
    have hs : i ∈ s := (List.mem_filter.mp hi).1
    exact mem_mul (hC i hs) (shiftFactor_mem _ _ _ _ (hP 0))
  have h₁ : ∀ g ∈ G, (C₁ g).mem (c₁ g) := by
    intro g _
    exact mem_mul (fiber_mem f C₀ c₀ S g h₀) (shiftFactor_mem _ _ _ _ (hP 1))
  have h₂ := mapped_sum_mem
    (fun h => mul (fiberInterval Prod.snd C₁ G h) (shiftFactorInterval h (k 2) (P 2)))
    (fun h => fiber Prod.snd c₁ G h * shiftFactor h (k 2) (a 2))
    (keys Prod.snd G)
    (fun h _ => mem_mul (fiber_mem Prod.snd C₁ c₁ G h h₁)
      (shiftFactor_mem _ _ _ _ (hP 2)))
  rw [← groupedCoeff_eq_gatheredOn e k c a s]
  exact h₂

/-- Use an archived target only after both rational endpoint comparisons. -/
theorem groupedInterval_mem_of_bounds {α : Type*} (e : α → Exp3) (k : Exp3)
    (C : α → RatInterval) (c : α → ℝ) (P : Fin 3 → ℕ → RatInterval)
    (a : Fin 3 → ℝ) (s : List α) (K : RatInterval)
    (hC : ∀ i ∈ s, (C i).mem (c i)) (hP : PowerEnclosures P a)
    (hlo : K.lo ≤ (groupedInterval e k C P s).lo)
    (hhi : (groupedInterval e k C P s).hi ≤ K.hi) :
    K.mem (gatheredOn e k c a s) := by
  exact mem_subset (groupedInterval_mem e k C c P a s hC hP) hlo hhi

end ThomsonNine.Interval.SparsePolynomial.Grouped
