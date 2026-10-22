import ThomsonNine.FixedInterval

noncomputable section
namespace ThomsonNine.FixedInterval
open ThomsonNine.Interval.SparsePolynomial ThomsonNine.Interval.SparsePolynomial.Grouped

abbrev Tree (α : Type*) := List (ℕ × List (ℕ × List α))
def flatten {α : Type*} (T : Tree α) : List α := T.flatMap (fun g => g.2.flatMap Prod.snd)
def Compatible {α : Type*} (e : α → Exp3) (T : Tree α) : Prop :=
  ∀ g ∈ T, ∀ h ∈ g.2, ∀ i ∈ h.2, e i 1 = h.1 ∧ e i 2 = g.1

def treeCoeff {α : Type*} (e : α → Exp3) (k : Exp3)
    (c : α → ℝ) (a : Fin 3 → ℝ) (T : Tree α) : ℝ :=
  (T.map (fun g => if k 2 ≤ g.1 then
    ((g.2.map (fun h => if k 1 ≤ h.1 then
      ((h.2.filter (fun i => decide (k 0 ≤ e i 0))).map
        (fun i => c i * shiftFactor (e i 0) (k 0) (a 0))).sum * shiftFactor h.1 (k 1) (a 1)
      else 0)).sum) * shiftFactor g.1 (k 2) (a 2) else 0)).sum

def treeCompute {α : Type*} (s : ℤ) (e : α → Exp3) (k : Exp3)
    (C : α → Bounds) (P : Fin 3 → ℕ → Bounds) (T : Tree α) : Bounds :=
  sum (T.map (fun g => if k 2 ≤ g.1 then
    mul s (sum (g.2.map (fun h => if k 1 ≤ h.1 then
      mul s (sum ((h.2.filter (fun i => decide (k 0 ≤ e i 0))).map
        (fun i => mul s (C i) (factor (e i 0) (k 0) (P 0))))) (factor h.1 (k 1) (P 1))
      else zero))) (factor g.1 (k 2) (P 2)) else zero))

lemma gatheredOn_ite {α : Type*} (e : α → Exp3) (k : Exp3)
    (c : α → ℝ) (a : Fin 3 → ℝ) (l : List α) :
    gatheredOn e k c a l =
      (l.map (fun i => if ∀ j, k j ≤ e i j then expandedCoefficient (e i) k (c i) a else 0)).sum := by
  induction l with
  | nil => simp [gatheredOn, eligible]
  | cons i l ih =>
    by_cases h : ∀ j, k j ≤ e i j <;> simp [gatheredOn, eligible, h] at ih ⊢ <;> exact ih

lemma map_filter_sum {α : Type*} (p : α → Prop) [DecidablePred p]
    (v : α → ℝ) (l : List α) :
    ((l.filter (fun i => decide (p i))).map v).sum =
      (l.map (fun i => if p i then v i else 0)).sum := by
  induction l with
  | nil => simp
  | cons i l ih => by_cases h : p i <;> simp [h, ih]

lemma sum_flatMap {α : Type*} (l : List α) (f : α → List ℝ) :
    (l.flatMap f).sum = (l.map (fun i => (f i).sum)).sum := by
  induction l with
  | nil => simp
  | cons i l ih => simp [List.sum_append, ih]

 theorem treeCoeff_eq {α : Type*} (e : α → Exp3) (k : Exp3)
    (c : α → ℝ) (a : Fin 3 → ℝ) (T : Tree α) (hT : Compatible e T) :
    treeCoeff e k c a T = gatheredOn e k c a (flatten T) := by
  rw [gatheredOn_ite]
  simp only [treeCoeff, flatten, List.map_flatMap, sum_flatMap]
  congr 1
  apply List.map_congr_left
  intro g hg
  by_cases ht : k 2 ≤ g.1
  · simp only [ite_eq_left ht, list_sum_mul, List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro h hh
    by_cases hv : k 1 ≤ h.1
    · simp only [ite_eq_left hv, list_sum_mul, List.map_map, Function.comp_def, map_filter_sum]
      congr 1
      apply List.map_congr_left
      intro i hi
      obtain ⟨he1, he2⟩ := hT g hg h hh i hi
      have he : (∀ j, k j ≤ e i j) ↔ k 0 ≤ e i 0 := by
        constructor
        · intro H; exact H 0
        · intro H j; fin_cases j <;> simp_all
      simp only [he, expandedCoefficient, he1, he2]
      split <;> simp_all
    · simp only [ite_eq_right hv, zero_mul]
      symm
      apply List.sum_eq_zero
      intro v hmem
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hmem
      have hfalse : ¬ ∀ j, k j ≤ e i j := by
        intro H; exact hv (by simpa [(hT g hg h hh i hi).1] using H 1)
      simp [hfalse]
  · simp only [ite_eq_right ht]
    symm
    apply List.sum_eq_zero
    intro v hmem
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hmem
    apply List.sum_eq_zero
    intro v hmem
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hmem
    have hfalse : ¬ ∀ j, k j ≤ e i j := by
      intro H; exact ht (by simpa [(hT g hg h hh i hi).2] using H 2)
    simp [hfalse]

 theorem treeCompute_mem {α : Type*} {s : ℤ} (hs : 0 < s) (e : α → Exp3) (k : Exp3)
    (C : α → Bounds) (c : α → ℝ) (P : Fin 3 → ℕ → Bounds)
    (a : Fin 3 → ℝ) (T : Tree α) (hT : Compatible e T)
    (hC : ∀ i ∈ flatten T, Mem s (C i) (c i))
    (hP : ∀ i n, Mem s (P i n) ((a i)^n)) :
    Mem s (treeCompute s e k C P T) (gatheredOn e k c a (flatten T)) := by
  rw [← treeCoeff_eq e k c a T hT]
  apply sum_mem
  intro g hg
  by_cases ht : k 2 ≤ g.1
  · simp only [ite_eq_left ht]
    apply mem_mul hs _ (factor_mem _ _ _ _ (hP 2))
    apply sum_mem
    intro h hh
    by_cases hv : k 1 ≤ h.1
    · simp only [ite_eq_left hv]
      apply mem_mul hs _ (factor_mem _ _ _ _ (hP 1))
      apply sum_mem
      intro i hi
      have hi' := (List.mem_filter.mp hi).1
      have hflat : i ∈ flatten T := by
        simp only [flatten, List.mem_flatMap]
        exact ⟨g,hg,h,hh,hi'⟩
      exact mem_mul hs (hC i hflat) (factor_mem _ _ _ _ (hP 0))
    · simp only [ite_eq_right hv]; exact mem_zero s
  · simp only [ite_eq_right ht]; exact mem_zero s

 theorem gatheredOn_perm {α : Type*} (e : α → Exp3) (k : Exp3)
    (c : α → ℝ) (a : Fin 3 → ℝ) {l m : List α} (h : l.Perm m) :
    gatheredOn e k c a l = gatheredOn e k c a m := by
  rw [gatheredOn_ite, gatheredOn_ite]
  exact (h.map _).sum_eq
end ThomsonNine.FixedInterval
