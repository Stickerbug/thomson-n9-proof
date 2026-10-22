import MainCoverage.Frame

noncomputable section
namespace ThomsonNine.PackedMain
open ThomsonNine.PackedTensor
attribute [local irreducible] packetValue

def AxisLower (lookup : ℕ → AxisEntry) (hfun : ℝ → ℝ) : Prop :=
  ∀ id t, 0≤t ∧ t≤1 → axisCurve (lookup id) t≤hfun (point (lookup id).level (lookup id).index t)
def Dominates (f : Fin 4 → (Fin 3 → ℝ) → ℝ) (G R : (Fin 3 → ℝ) → ℝ) (hfun : ℝ → ℝ) : Prop :=
  ∀ q x, RootCube x → 0≤G x → f q x+hfun (x 0)+hfun (x 1)+hfun (x 2)≤R x
def LocalLower (cores : ℕ → Fin 3 → ℚ × ℚ) (G R : (Fin 3 → ℝ) → ℝ) : Prop :=
  ∀ id x, id<12 → RootCube x → (∀ a, ((cores id a).1 : ℝ)≤x a ∧ x a≤((cores id a).2 : ℝ)) →
    0≤G x → 0≤R x

theorem positive_sound (lookup : ℕ → AxisEntry) (f : Fin 4 → (Fin 3 → ℝ) → ℝ)
    (G R : (Fin 3 → ℝ) → ℝ) (hfun : ℝ → ℝ)
    (hAxis : AxisLower lookup hfun) (hDom : Dominates f G R hfun)
    (s : State) (hs : valid s) (hf : Frame f G s) (slot : Fin 4) (h0 h1 h2 : ℕ)
    (h : positiveOK lookup s slot h0 h1 h2=true)
    (z : Fin 3 → ℝ) (hz : UnitCube z) (hG : 0≤G (boxPoint s z)) : 0≤R (boxPoint s z) := by
  have hp := Bool.and_eq_true_iff.mp h
  have he : ∀ a : Fin 3, (![lookup h0,lookup h1,lookup h2] a).level=s.levels a ∧
      (![lookup h0,lookup h1,lookup h2] a).index=s.indices a ∧
      _ := of_decide_eq_true hp.1
  have hh0 := hAxis h0 (z 0) (hz 0)
  have hh1 := hAxis h1 (z 1) (hz 1)
  have hh2 := hAxis h2 (z 2) (hz 2)
  have he0 := he 0;have he1 := he 1;have he2 := he 2
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at he0 he1 he2
  rw [he0.1,he0.2.1] at hh0
  rw [he1.1,he1.2.1] at hh1
  rw [he2.1,he2.2.1] at hh2
  have hpos := positive_leaf lookup s slot h0 h1 h2 h z hz
  have hk := hf.1 slot z hz
  have hr := hDom slot (boxPoint s z) (boxPoint_root_range s hs z hz) hG
  change axisCurve (lookup h0) (z 0)≤hfun (boxPoint s z 0) at hh0
  change axisCurve (lookup h1) (z 1)≤hfun (boxPoint s z 1) at hh1
  change axisCurve (lookup h2) (z 2)≤hfun (boxPoint s z 2) at hh2
  linarith only [hpos,hk,hh0,hh1,hh2,hr]

theorem local_sound (cores : ℕ → Fin 3 → ℚ × ℚ) (G R : (Fin 3 → ℝ) → ℝ)
    (hLocal : LocalLower cores G R) (s : State) (hs : valid s) (id : ℕ)
    (h : localOK cores s id=true) (z : Fin 3 → ℝ) (hz : UnitCube z)
    (hG : 0≤G (boxPoint s z)) : 0≤R (boxPoint s z) := by
  have hp : id<12 ∧ ∀ a, (cores id a).1≤low s a ∧ high s a≤(cores id a).2 := of_decide_eq_true h
  apply hLocal id _ hp.1 (boxPoint_root_range s hs z hz) _ hG
  intro a
  have hb := point_bounds s z hz a
  have hl : ((cores id a).1 : ℝ)≤(low s a : ℝ) := by exact_mod_cast (hp.2 a).1
  have hr : (high s a : ℝ)≤((cores id a).2 : ℝ) := by exact_mod_cast (hp.2 a).2
  exact ⟨hl.trans hb.1,hb.2.trans hr⟩

theorem check_sound (lookup : ℕ → AxisEntry) (cores : ℕ → Fin 3 → ℚ × ℚ)
    (f : Fin 4 → (Fin 3 → ℝ) → ℝ) (G R : (Fin 3 → ℝ) → ℝ) (hfun : ℝ → ℝ)
    (hFallback : Fallback f G) (hAxis : AxisLower lookup hfun)
    (hDom : Dominates f G R hfun) (hLocal : LocalLower cores G R)
    (tree : Tree) (s : State) (hs : valid s) (hf : Frame f G s)
    (h : check lookup cores s tree=true) (z : Fin 3 → ℝ) (hz : UnitCube z)
    (ho : Monotone (boxPoint s z)) (hG : 0≤G (boxPoint s z)) : 0≤R (boxPoint s z) := by
  induction tree generalizing s z with
  | positive slot h0 h1 h2 => exact positive_sound lookup f G R hfun hAxis hDom s hs hf slot h0 h1 h2 h z hz hG
  | gram =>
    have hp := gram_leaf s h z hz
    have hg := hf.2 z hz
    linarith only [hp,hg,hG]
  | order a b => exact (order_leaf s a b h z hz ho).elim
  | «local» id => exact local_sound cores G R hLocal s hs id h z hz hG
  | split mask l r ihl ihr =>
    have hp : decide (mask=need l ||| need r)=true ∧ stepOK s (need l) false=true ∧
        check lookup cores (child s (need l) false) l=true ∧ stepOK s (need r) true=true ∧
        check lookup cores (child s (need r) true) r=true := by
      simpa only [check,Bool.and_eq_true_iff,and_assoc] using h
    by_cases hside : z (splitAxis s)≤(1:ℝ)/2
    · let zz := childCoordinates (splitAxis s) false z
      have hzz := childCoordinates_mem (splitAxis s) z hz false hside
      have hpoint : boxPoint (child s (need l) false) zz=boxPoint s z := by
        rw [box_child,half_childCoordinates]
      have hc := child_frame f G hFallback s hs hf (need l) false hp.2.1
      have hh := ihl (child s (need l) false) (child_valid s _ _ hs) hc hp.2.2.1 zz hzz
        (by simpa only [hpoint] using ho) (by simpa only [hpoint] using hG)
      simpa only [hpoint] using hh
    · let zz := childCoordinates (splitAxis s) true z
      have hzz := childCoordinates_mem (splitAxis s) z hz true (le_of_lt (lt_of_not_ge hside))
      have hpoint : boxPoint (child s (need r) true) zz=boxPoint s z := by
        rw [box_child,half_childCoordinates]
      have hc := child_frame f G hFallback s hs hf (need r) true hp.2.2.2.1
      have hh := ihr (child s (need r) true) (child_valid s _ _ hs) hc hp.2.2.2.2 zz hzz
        (by simpa only [hpoint] using ho) (by simpa only [hpoint] using hG)
      simpa only [hpoint] using hh
end ThomsonNine.PackedMain
