import ThomsonCertificate.GenericCertificate
import MainCoverage.Final

/-!
# Structural n=9 adapter

This file maps the n=9 `CutTree` shape to the generic `Tree` type.  The leaf
soundness proof still calls the existing exact leaf checker, while the generic
split theorem proves the dyadic box transport.  It therefore measures real
tree-interface reuse without changing the frozen theorem.
-/

namespace ThomsonNine

open ThomsonNine.PackedMain
open ThomsonNine.PackedTensor
open ThomsonCertificate

structure N9Box where
  state : State
  path : List Bool
  leafId : Option ℕ

def n9Inside (b : N9Box) (p : Fin 3 → ℝ) : Prop :=
  ∃ z, UnitCube z ∧ boxPoint b.state z = p

def n9Split (b l r : N9Box) : Prop :=
  l.state = fullChild b.state false ∧
    l.path = b.path ++ [false] ∧
    r.state = fullChild b.state true ∧
    r.path = b.path ++ [true]

def n9TreeAt : State → List Bool → CutTree → ThomsonCertificate.Tree N9Box
  | s, path, .stop id => .leaf ⟨s, path, some id⟩
  | s, path, .split l r =>
      .split ⟨s, path, none⟩
        (n9TreeAt (fullChild s false) (path ++ [false]) l)
        (n9TreeAt (fullChild s true) (path ++ [true]) r)

def n9Terminal (b : N9Box) : Prop :=
  ∃ id, b.leafId = some id ∧
    b.path = (certifiedChunk id).path ∧
    b.state = atPath rootState b.path

theorem n9TreeAt_root (s : State) (path : List Bool) (cut : CutTree) :
    (n9TreeAt s path cut).root =
      match cut with
      | .stop id => ⟨s, path, some id⟩
      | .split _ _ => ⟨s, path, none⟩ := by
  cases cut <;> rfl

def n9StructuredSpec : Spec N9Box (Fin 3 → ℝ) :=
  { inside := n9Inside
    domain := fun p => RootCube p ∧ Monotone p ∧ 0 ≤ gramFn p
    goal := fun p => 0 ≤ ActualCoulombGlobal.residual p
    terminal := n9Terminal
    splits := n9Split
    leaf_sound := by
      intro b hb p hp hi
      rcases hb with ⟨id, hid, hpath, hstate⟩
      rcases hi with ⟨z, hz, hpoint⟩
      let G := fun x : Fin 3 → ℝ => Semantics.gram (x 0) (x 1) (x 2)
      have hframe := path_frame penalizedKernel G actual_fallback rootState
        root_valid actual_root_frame (certifiedChunk id).path
        (certifiedChunk id).certificate.1
      have htree : check axisLookup localCores (atPath rootState (certifiedChunk id).path)
          (certifiedChunk id).tree = true := (certifiedChunk id).certificate.2
      have hstate' : b.state = atPath rootState (certifiedChunk id).path := by
        rw [hstate, hpath]
      have hframe' : Frame penalizedKernel G b.state := by simpa [hstate'] using hframe.2
      have hvalid' : valid b.state := by simpa [hstate'] using hframe.1
      have htree' : check axisLookup localCores b.state (certifiedChunk id).tree = true := by
        simpa [hstate'] using htree
      have hzmono : Monotone (boxPoint b.state z) := by simpa [hpoint] using hp.2.1
      have hgpoint : 0 ≤ G p := by simpa [G, gramFn] using hp.2.2
      have hzgram : 0 ≤ G (boxPoint b.state z) := by simpa [hpoint] using hgpoint
      have hr := check_sound axisLookup localCores penalizedKernel G
        ActualCoulombGlobal.residual
        (fun t => ActualCoulombGlobal.coulomb t - MainEnvelope.diagonal t)
        actual_fallback actual_axes_lower actual_dominates actual_local_lower
        (certifiedChunk id).tree b.state hvalid' hframe' htree' z hz hzmono hzgram
      simpa [hpoint] using hr
    split_sound := by
      intro b l r hsplit p hp
      rcases hsplit with ⟨hlstate, hlpath, hrstate, hrpath⟩
      rcases hp with ⟨z, hz, hpoint⟩
      by_cases hside : z (splitAxis b.state) ≤ (1 : ℝ) / 2
      · left
        let zz := childCoordinates (splitAxis b.state) false z
        have hzz := childCoordinates_mem (splitAxis b.state) z hz false hside
        refine ⟨zz, hzz, ?_⟩
        calc
          boxPoint l.state zz = boxPoint (fullChild b.state false) zz := by rw [hlstate]
          _ = boxPoint b.state (halfPoint (splitAxis b.state) false zz) := by
            exact box_child b.state 31 false zz
          _ = boxPoint b.state z := by rw [half_childCoordinates]
          _ = p := hpoint
      · right
        let zz := childCoordinates (splitAxis b.state) true z
        have hzz := childCoordinates_mem (splitAxis b.state) z hz true
          (le_of_lt (lt_of_not_ge hside))
        refine ⟨zz, hzz, ?_⟩
        calc
          boxPoint r.state zz = boxPoint (fullChild b.state true) zz := by rw [hrstate]
          _ = boxPoint b.state (halfPoint (splitAxis b.state) true zz) := by
            exact box_child b.state 31 true zz
          _ = boxPoint b.state z := by rw [half_childCoordinates]
          _ = p := hpoint }

theorem n9_cut_checked_to_generic :
    ∀ (s : State) (path : List Bool) (cut : CutTree),
      s = atPath rootState path →
      cutCheck (fun id => (certifiedChunk id).path) path cut = true →
      Checked n9StructuredSpec (n9TreeAt s path cut) := by
  intro s path cut
  induction cut generalizing s path with
  | stop id =>
      intro hs hcut
      have hpath : (certifiedChunk id).path = path := of_decide_eq_true hcut
      refine ⟨id, rfl, hpath.symm, ?_⟩
      exact hs
  | split l r ihl ihr =>
      intro hs hcut
      have hc := Bool.and_eq_true_iff.mp hcut
      refine ⟨?_, ihl (fullChild s false) (path ++ [false]) ?_ hc.1,
        ihr (fullChild s true) (path ++ [true]) ?_ hc.2⟩
      · change n9Split
          ⟨s, path, none⟩
          (Tree.root (n9TreeAt (fullChild s false) (path ++ [false]) l))
          (Tree.root (n9TreeAt (fullChild s true) (path ++ [true]) r))
        simp only [n9TreeAt_root]
        cases l <;> cases r <;> simp [n9Split, fullChild]
      · rw [atPath_append, hs]
        rfl
      · rw [atPath_append, hs]
        rfl

def n9StructuredCertificate : Certificate 9 :=
  { Box := N9Box
    Point := Fin 3 → ℝ
    spec := n9StructuredSpec
    tree := n9TreeAt rootState [] rootCut
    checked := n9_cut_checked_to_generic rootState [] rootCut rfl root_cut_checked }

theorem n9_structured_certificate_sound (p : Fin 3 → ℝ)
    (hp : RootCube p) (ho : Monotone p) (hg : 0 ≤ gramFn p) :
    0 ≤ ActualCoulombGlobal.residual p := by
  have hroot : ∀ a : Fin 3, rootState.levels a = 0 := by
    intro a
    rfl
  have hindex : ∀ a : Fin 3, rootState.indices a = 0 := by
    intro a
    rfl
  have hin : n9Inside ⟨rootState, [], none⟩ p := by
    refine ⟨rootCoordinates p, rootCoordinates_mem p hp, ?_⟩
    exact root_point_eq rootState hroot hindex p
  exact n9StructuredCertificate.sound p ⟨hp, ho, hg⟩ hin

end ThomsonNine
