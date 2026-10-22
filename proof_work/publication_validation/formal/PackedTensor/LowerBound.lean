import PackedTensor.TensorModel

noncomputable section
namespace ThomsonNine.PackedTensor
open ThomsonNine.PackedRadix

def packetCoefficients (n offset scale packet : ℕ) (p : CubeIndex (n+1)) : ℝ :=
  decode offset scale packet (flat p)
def packetValue (n offset scale packet : ℕ) (x : Fin 3 → ℝ) : ℝ :=
  tensorValue n (packetCoefficients n offset scale packet) x

theorem half_lower (n lanes g offset scale : ℕ) (hr : rowSpec (n+1)) (hb : basisSpec n)
    (planes : Fin 3 → Fin (n+1) → ℕ) (hplanes : PlaneSpec planes)
    (axis : Fin 3) (right : Bool) (packet : ℕ)
    (hg : 2*g+1<2^128) (h : halfOK lanes g planes axis right packet=true)
    (hs : (0 : ℝ)<scale) (hn : (n+1)*(n+1)*(n+1)≤lanes)
    (x : Fin 3 → ℝ) (hx : ∀ a, 0≤x a ∧ x a≤1) :
    packetValue n offset scale (half lanes g planes axis right packet) x≤
      packetValue n offset scale packet (halfPoint axis right x) := by
  let b := packetCoefficients n offset scale packet
  have hc : ∀ p, packetCoefficients n offset scale (half lanes g planes axis right packet) p≤
      realHalf n b axis right p := by
    intro p
    cases right
    · exact half_left_bound lanes g offset scale planes hplanes axis packet hg h hs hn b
        (fun _ => le_refl _) p
    · exact half_right_bound lanes g offset scale planes hplanes axis packet hg h hs hn b
        (fun _ => le_refl _) p
  exact (tensor_mono n _ _ hc x hx).trans_eq (tensor_half n hr hb b axis right x)

end ThomsonNine.PackedTensor
