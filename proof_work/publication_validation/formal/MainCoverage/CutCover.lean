import MainCoverage.TreeSound

noncomputable section
namespace ThomsonNine.PackedMain

inductive CutTree where
  | stop (id : ℕ)
  | split (left right : CutTree)

def cutCheck (paths : ℕ → List Bool) (path : List Bool) : CutTree → Bool
  | .stop id => decide (paths id=path)
  | .split l r => cutCheck paths (path++[false]) l && cutCheck paths (path++[true]) r

theorem atPath_append (root : State) (path : List Bool) (side : Bool) :
    atPath root (path++[side])=child (atPath root path) 31 side := by
  simp only [atPath,List.foldl_append,List.foldl_cons,List.foldl_nil,fullChild]

theorem cutCover (paths : ℕ → List Bool) (root : State) (G R : (Fin 3 → ℝ) → ℝ)
    (hcert : ∀ id z, UnitCube z → Monotone (boxPoint (atPath root (paths id)) z) →
      0≤G (boxPoint (atPath root (paths id)) z) → 0≤R (boxPoint (atPath root (paths id)) z))
    (tree : CutTree) (path : List Bool) (h : cutCheck paths path tree=true)
    (z : Fin 3 → ℝ) (hz : UnitCube z) (ho : Monotone (boxPoint (atPath root path) z))
    (hG : 0≤G (boxPoint (atPath root path) z)) : 0≤R (boxPoint (atPath root path) z) := by
  induction tree generalizing path z with
  | stop id =>
    have hp : paths id=path := of_decide_eq_true h
    simpa only [hp] using hcert id z (by simpa only [hp] using hz)
      (by simpa only [hp] using ho) (by simpa only [hp] using hG)
  | split l r ihl ihr =>
    have hp := Bool.and_eq_true_iff.mp h
    let s := atPath root path
    by_cases hside : z (splitAxis s)≤(1:ℝ)/2
    · let zz := childCoordinates (splitAxis s) false z
      have hzz := childCoordinates_mem (splitAxis s) z hz false hside
      have hpoint : boxPoint (atPath root (path++[false])) zz=boxPoint s z := by
        rw [atPath_append,box_child,half_childCoordinates]
      have hh := ihl (path++[false]) hp.1 zz hzz
        (by simpa only [hpoint] using ho) (by simpa only [hpoint] using hG)
      simpa only [hpoint] using hh
    · let zz := childCoordinates (splitAxis s) true z
      have hzz := childCoordinates_mem (splitAxis s) z hz true (le_of_lt (lt_of_not_ge hside))
      have hpoint : boxPoint (atPath root (path++[true])) zz=boxPoint s z := by
        rw [atPath_append,box_child,half_childCoordinates]
      have hh := ihr (path++[true]) hp.2 zz hzz
        (by simpa only [hpoint] using ho) (by simpa only [hpoint] using hG)
      simpa only [hpoint] using hh

theorem path_frame (f : Fin 4 → (Fin 3 → ℝ) → ℝ) (G : (Fin 3 → ℝ) → ℝ)
    (hF : Fallback f G) (root : State) (hs : valid root) (hf : Frame f G root)
    (path : List Bool) (h : pathOK root path=true) : valid (atPath root path) ∧ Frame f G (atPath root path) := by
  induction path generalizing root with
  | nil => exact ⟨hs,hf⟩
  | cons side rest ih =>
    have hp := Bool.and_eq_true_iff.mp h
    exact ih (fullChild root side) (child_valid root 31 side hs)
      (child_frame f G hF root hs hf 31 side hp.1) hp.2
end ThomsonNine.PackedMain
