import PackedTensor.Selection

namespace ThomsonNine.PackedTensor
open ThomsonNine.PackedRadix

def broadcastOK {d : ℕ} (lanes g : ℕ) (planes : Fin 3 → Fin d → ℕ) (axis : Fin 3)
    (values : Fin d → ℕ) (packet : ℕ) : Bool :=
  decide ((∀ c, values c<2^128 ∧ packet &&& planes axis c=
      fastMask 128 lanes (values c) &&& planes axis c) ∧ packet &&& fastMask 128 lanes g=packet)

theorem broadcast_sound {d : ℕ} (lanes g : ℕ) (planes : Fin 3 → Fin d → ℕ)
    (hplanes : PlaneSpec planes) (axis : Fin 3) (values : Fin d → ℕ) (packet : ℕ)
    (hn : d*d*d≤lanes) (h : broadcastOK lanes g planes axis values packet=true) (p : CubeIndex d) :
    limb 128 packet (flat p)=values (coord axis p) := by
  have hp : (∀ c, values c<2^128 ∧ packet &&& planes axis c=
      fastMask 128 lanes (values c) &&& planes axis c) ∧ packet &&& fastMask 128 lanes g=packet :=
    of_decide_eq_true h
  let c := coord axis p
  calc
    limb 128 packet (flat p)=limb 128 (packet &&& planes axis c) (flat p) :=
      (read_plane planes hplanes axis c packet p rfl).symm
    _ = limb 128 (fastMask 128 lanes (values c) &&& planes axis c) (flat p) :=
      congrArg (fun q => limb 128 q (flat p)) (hp.1 c).2
    _ = limb 128 (fastMask 128 lanes (values c)) (flat p) :=
      read_plane planes hplanes axis c _ p rfl
    _ = values c := by
      rw [fastMask_eq 128 lanes (values c) (by omega)]
      exact limb_mask 128 lanes (flat p) (values c) ((flat_lt p).trans_le hn) (hp.1 c).1
end ThomsonNine.PackedTensor
