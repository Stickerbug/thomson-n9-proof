import PackedTensor.Geometry
import PackedRadix.Shifts

namespace ThomsonNine.PackedTensor
open ThomsonNine.PackedRadix
def PlaneSpec {d : ℕ} (planes : Fin 3 → Fin d → ℕ) : Prop :=
  ∀ axis c (p : CubeIndex d), limb 128 (planes axis c) (flat p)=
    if (coord axis p).val=c.val then 2^128-1 else 0

theorem read_plane {d : ℕ} (planes : Fin 3 → Fin d → ℕ) (hplanes : PlaneSpec planes)
    (axis : Fin 3) (c : Fin d) (x : ℕ) (p : CubeIndex d) (hc : coord axis p=c) :
    limb 128 (x &&& planes axis c) (flat p)=limb 128 x (flat p) := by
  rw [limb_and,hplanes axis c p,if_pos (congrArg Fin.val hc),Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt (Nat.mod_lt _ (pow_pos (by omega) _))

def selectionOK {d : ℕ} [NeZero d] (planes : Fin 3 → Fin d → ℕ) (axis : Fin 3)
    (right : Bool) (rows : ℕ → ℕ) (out : ℕ) : Bool :=
  decide (∀ c : Fin d, out &&& planes axis c=
    if right then rows (d-1-c.val) &&& planes axis c
    else (rows c.val &&& planes axis 0) <<< (128*(stride d axis*c.val)))

theorem selection_left {d : ℕ} [NeZero d] (planes : Fin 3 → Fin d → ℕ) (hplanes : PlaneSpec planes)
    (axis : Fin 3) (rows : ℕ → ℕ) (out : ℕ)
    (h : selectionOK planes axis false rows out=true) (p : CubeIndex d) :
    limb 128 out (flat p)=limb 128 (rows (coord axis p).val) (zeroIndex axis p) := by
  have he : ∀ c : Fin d, out &&& planes axis c=
      (rows c.val &&& planes axis 0) <<< (128*(stride d axis*c.val)) := of_decide_eq_true h
  let c := coord axis p
  calc
    limb 128 out (flat p)=limb 128 (out &&& planes axis c) (flat p) :=
      (read_plane planes hplanes axis c out p rfl).symm
    _ = limb 128 ((rows c.val &&& planes axis 0) <<< (128*(stride d axis*c.val))) (flat p) :=
      congrArg (fun x => limb 128 x (flat p)) (he c)
    _ = limb 128 (rows c.val &&& planes axis 0) (zeroIndex axis p) := by
      rw [flat_decompose axis p,limb_shiftLeft]
    _ = limb 128 (rows c.val) (zeroIndex axis p) :=
      read_plane planes hplanes axis 0 (rows c.val) (replace axis p 0) (coord_replace axis p 0)

theorem selection_right {d : ℕ} [NeZero d] (planes : Fin 3 → Fin d → ℕ) (hplanes : PlaneSpec planes)
    (axis : Fin 3) (rows : ℕ → ℕ) (out : ℕ)
    (h : selectionOK planes axis true rows out=true) (p : CubeIndex d) :
    limb 128 out (flat p)=limb 128 (rows (d-1-(coord axis p).val)) (flat p) := by
  have he : ∀ c : Fin d, out &&& planes axis c=rows (d-1-c.val) &&& planes axis c := of_decide_eq_true h
  let c := coord axis p
  calc
    limb 128 out (flat p)=limb 128 (out &&& planes axis c) (flat p) :=
      (read_plane planes hplanes axis c out p rfl).symm
    _ = limb 128 (rows (d-1-c.val) &&& planes axis c) (flat p) :=
      congrArg (fun x => limb 128 x (flat p)) (he c)
    _ = limb 128 (rows (d-1-c.val)) (flat p) := read_plane planes hplanes axis c _ p rfl
end ThomsonNine.PackedTensor
