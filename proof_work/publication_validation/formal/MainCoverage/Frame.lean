import MainCoverage.DyadicGeometry
import MainCoverage.LeafSemantics
import PackedTensor.BernsteinListSpec02
import PackedTensor.BernsteinListSpec10

noncomputable section
namespace ThomsonNine.PackedMain
open ThomsonNine.PackedTensor ThomsonNine.PackedRadix

def UnitCube (z : Fin 3 → ℝ) : Prop := ∀ a, 0≤z a ∧ z a≤1
def RootCube (x : Fin 3 → ℝ) : Prop := ∀ a, -1≤x a ∧ x a≤14/25
def Frame (f : Fin 4 → (Fin 3 → ℝ) → ℝ) (G : (Fin 3 → ℝ) → ℝ) (s : State) : Prop :=
  (∀ q z, UnitCube z → packetValue 10 offset scale (s.kernels q) z≤f q (boxPoint s z)) ∧
  (∀ z, UnitCube z → packetValue 2 offset scale s.gram z≤-G (boxPoint s z))
def Fallback (f : Fin 4 → (Fin 3 → ℝ) → ℝ) (G : (Fin 3 → ℝ) → ℝ) : Prop :=
  (∀ q x, RootCube x → -(offset : ℝ)/(scale : ℝ)≤f q x) ∧
  (∀ x, RootCube x → -(offset : ℝ)/(scale : ℝ)≤-G x)

theorem halfPoint_mem (a : Fin 3) (side : Bool) (z : Fin 3 → ℝ) (hz : UnitCube z) :
    UnitCube (halfPoint a side z) := by
  intro b
  by_cases hb : b=a
  · subst b
    cases side <;> simp only [halfPoint,Function.update_self,Bool.false_eq_true,ite_false,ite_true]
    all_goals constructor <;> nlinarith [(hz a).1,(hz a).2]
  · simpa only [halfPoint,Function.update_of_ne hb] using hz b

theorem zero_packet_value (n : ℕ) (z : Fin 3 → ℝ) :
    packetValue n offset scale 0 z=-(offset : ℝ)/(scale : ℝ) := by
  have hc : packetCoefficients n offset scale 0=fun _ => -(offset : ℝ)/(scale : ℝ) := by
    funext p
    simp [packetCoefficients,decode,limb]
  rw [packetValue,hc]
  exact tensor_constant n _ z

attribute [local irreducible] packetValue

theorem child_frame (f : Fin 4 → (Fin 3 → ℝ) → ℝ) (G : (Fin 3 → ℝ) → ℝ)
    (hF : Fallback f G) (s : State) (hs : valid s) (hf : Frame f G s)
    (mask : ℕ) (side : Bool) (h : stepOK s mask side=true) : Frame f G (child s mask side) := by
  have hp : (∀ q : Fin 4, wanted mask q.val=true → halfOK 1331 bound planes11 (splitAxis s) side (s.kernels q)=true) ∧
      (wanted mask 4=true → halfOK 27 bound planes3 (splitAxis s) side s.gram=true) := of_decide_eq_true h
  have hc := child_valid s mask side hs
  constructor
  · intro q z hz
    by_cases hw : wanted mask q.val=true
    · have hhalf := half_lower 10 1331 bound offset scale row_spec_11 basis_list_spec_10
        planes11 planes11_correct (splitAxis s) side (s.kernels q) bound_valid (hp.1 q hw)
        scale_pos (by omega) z hz
      have hparent := hf.1 q (halfPoint (splitAxis s) side z) (halfPoint_mem _ _ _ hz)
      have he : (child s mask side).kernels q=half 1331 bound planes11 (splitAxis s) side (s.kernels q) := by
        simp only [child,hw,ite_true]
      rw [he,box_child]
      exact hhalf.trans hparent
    · have he : (child s mask side).kernels q=0 := by simp [child,hw]
      rw [he,zero_packet_value]
      exact hF.1 q _ (boxPoint_root_range _ hc z hz)
  · intro z hz
    by_cases hw : wanted mask 4=true
    · have hhalf := half_lower 2 27 bound offset scale row_spec_3 basis_list_spec_2
        planes3 planes3_correct (splitAxis s) side s.gram bound_valid (hp.2 hw)
        scale_pos (by omega) z hz
      have hparent := hf.2 (halfPoint (splitAxis s) side z) (halfPoint_mem _ _ _ hz)
      have he : (child s mask side).gram=half 27 bound planes3 (splitAxis s) side s.gram := by
        simp only [child,hw,ite_true]
      rw [he,box_child]
      exact hhalf.trans hparent
    · have he : (child s mask side).gram=0 := by simp [child,hw]
      rw [he,zero_packet_value]
      exact hF.2 _ (boxPoint_root_range _ hc z hz)

def rootCoordinates (x : Fin 3 → ℝ) : Fin 3 → ℝ := fun a => (x a+1)/(39/25)

theorem rootCoordinates_mem (x : Fin 3 → ℝ) (hx : RootCube x) : UnitCube (rootCoordinates x) := by
  intro a
  have h := hx a
  dsimp only [rootCoordinates]
  constructor
  · exact div_nonneg (by linarith) (by norm_num)
  · apply (div_le_one (by norm_num : (0:ℝ)<39/25)).mpr
    linarith

theorem root_point_eq (root : State) (hl : ∀ a, root.levels a=0) (hi : ∀ a, root.indices a=0)
    (x : Fin 3 → ℝ) : boxPoint root (rootCoordinates x)=x := by
  funext a
  simp only [boxPoint,hl,hi,point,left,width,rootCoordinates]
  norm_num
  ring

theorem fallback_of_root_frame (f : Fin 4 → (Fin 3 → ℝ) → ℝ) (G : (Fin 3 → ℝ) → ℝ)
    (root : State) (hl : ∀ a, root.levels a=0) (hi : ∀ a, root.indices a=0) (hf : Frame f G root) : Fallback f G := by
  constructor
  · intro q x hx
    have hz := rootCoordinates_mem x hx
    have hp := hf.1 q (rootCoordinates x) hz
    rw [root_point_eq root hl hi x] at hp
    exact (packet_value_floor 10 offset scale (root.kernels q) scale_pos _ hz).trans hp
  · intro x hx
    have hz := rootCoordinates_mem x hx
    have hp := hf.2 (rootCoordinates x) hz
    rw [root_point_eq root hl hi x] at hp
    exact (packet_value_floor 2 offset scale root.gram scale_pos _ hz).trans hp
end ThomsonNine.PackedMain
