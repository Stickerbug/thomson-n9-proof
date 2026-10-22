import ThomsonNine.GroupedTranslation

/-! Intermediate enclosures are supplied as finite witnesses. Their two endpoint
comparisons are checked separately; no rounding algorithm is trusted. -/
noncomputable section
namespace ThomsonNine.Interval.SparsePolynomial.Grouped
open ThomsonNine.Interval ThomsonNine.Interval.RatInterval

def firstKeys {α : Type*} (e : α → Exp3) (k : Exp3) (s : List α) : List (ℕ × ℕ) :=
  keys (fun i => (e i 1, e i 2)) (eligible e k s)

def firstStage {α : Type*} (e : α → Exp3) (k : Exp3)
    (C : α → RatInterval) (P : Fin 3 → ℕ → RatInterval)
    (s : List α) (g : ℕ × ℕ) : RatInterval :=
  fiberInterval (fun i => (e i 1, e i 2))
    (fun i => mul (C i) (shiftFactorInterval (e i 0) (k 0) (P 0))) (eligible e k s) g

def secondStage {α : Type*} (e : α → Exp3) (k : Exp3)
    (P : Fin 3 → ℕ → RatInterval) (s : List α)
    (U : ℕ × ℕ → RatInterval) (h : ℕ) : RatInterval :=
  fiberInterval Prod.snd (fun g => mul (U g) (shiftFactorInterval g.1 (k 1) (P 1)))
    (firstKeys e k s) h

def cachedFinal {α : Type*} (e : α → Exp3) (k : Exp3)
    (P : Fin 3 → ℕ → RatInterval) (s : List α) (V : ℕ → RatInterval) : RatInterval :=
  sumIntervals ((keys Prod.snd (firstKeys e k s)).map
    (fun h => mul (V h) (shiftFactorInterval h (k 2) (P 2))))

/-- A finite certificate for each cache level suffices for the complete sum. -/
theorem cachedFinal_mem {α : Type*} (e : α → Exp3) (k : Exp3)
    (C : α → RatInterval) (c : α → ℝ) (P : Fin 3 → ℕ → RatInterval)
    (a : Fin 3 → ℝ) (s : List α) (U : ℕ × ℕ → RatInterval) (V : ℕ → RatInterval)
    (hC : ∀ i ∈ s, (C i).mem (c i)) (hP : PowerEnclosures P a)
    (hU : ∀ g ∈ firstKeys e k s,
      (U g).lo ≤ (firstStage e k C P s g).lo ∧
      (firstStage e k C P s g).hi ≤ (U g).hi)
    (hV : ∀ h ∈ keys Prod.snd (firstKeys e k s),
      (V h).lo ≤ (secondStage e k P s U h).lo ∧
      (secondStage e k P s U h).hi ≤ (V h).hi) :
    (cachedFinal e k P s V).mem (gatheredOn e k c a s) := by
  let S := eligible e k s
  let f := fun i => (e i 1, e i 2)
  let G := firstKeys e k s
  let c₀ := fun i => c i * shiftFactor (e i 0) (k 0) (a 0)
  let c₁ := fun g : ℕ × ℕ => fiber f c₀ S g * shiftFactor g.1 (k 1) (a 1)
  have h₀ : ∀ i ∈ S,
      (mul (C i) (shiftFactorInterval (e i 0) (k 0) (P 0))).mem (c₀ i) := by
    intro i hi
    exact mem_mul (hC i (List.mem_filter.mp hi).1) (shiftFactor_mem _ _ _ _ (hP 0))
  have hu : ∀ g ∈ G, (U g).mem (fiber f c₀ S g) := by
    intro g hg
    exact mem_subset (fiber_mem f _ c₀ S g h₀) (hU g hg).1 (hU g hg).2
  have h₁ : ∀ g ∈ G,
      (mul (U g) (shiftFactorInterval g.1 (k 1) (P 1))).mem (c₁ g) := by
    intro g hg
    exact mem_mul (hu g hg) (shiftFactor_mem _ _ _ _ (hP 1))
  have hv : ∀ h ∈ keys Prod.snd G, (V h).mem (fiber Prod.snd c₁ G h) := by
    intro h hh
    exact mem_subset (fiber_mem Prod.snd _ c₁ G h h₁) (hV h hh).1 (hV h hh).2
  have h₂ := mapped_sum_mem
    (fun h => mul (V h) (shiftFactorInterval h (k 2) (P 2)))
    (fun h => fiber Prod.snd c₁ G h * shiftFactor h (k 2) (a 2))
    (keys Prod.snd G)
    (fun h hh => mem_mul (hv h hh) (shiftFactor_mem _ _ _ _ (hP 2)))
  rw [← groupedCoeff_eq_gatheredOn e k c a s]
  exact h₂

theorem cachedFinal_mem_of_bounds {α : Type*} (e : α → Exp3) (k : Exp3)
    (C : α → RatInterval) (c : α → ℝ) (P : Fin 3 → ℕ → RatInterval)
    (a : Fin 3 → ℝ) (s : List α) (U : ℕ × ℕ → RatInterval) (V : ℕ → RatInterval)
    (K : RatInterval) (hC : ∀ i ∈ s, (C i).mem (c i)) (hP : PowerEnclosures P a)
    (hU : ∀ g ∈ firstKeys e k s,
      (U g).lo ≤ (firstStage e k C P s g).lo ∧
      (firstStage e k C P s g).hi ≤ (U g).hi)
    (hV : ∀ h ∈ keys Prod.snd (firstKeys e k s),
      (V h).lo ≤ (secondStage e k P s U h).lo ∧
      (secondStage e k P s U h).hi ≤ (V h).hi)
    (hK : K.lo ≤ (cachedFinal e k P s V).lo ∧
      (cachedFinal e k P s V).hi ≤ K.hi) :
    K.mem (gatheredOn e k c a s) := by
  exact mem_subset (cachedFinal_mem e k C c P a s U V hC hP hU hV) hK.1 hK.2

end ThomsonNine.Interval.SparsePolynomial.Grouped
