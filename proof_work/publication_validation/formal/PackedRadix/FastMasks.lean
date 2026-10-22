import PackedRadix.Geometry

namespace ThomsonNine.PackedRadix
theorem repunit_closed (b n : ℕ) (hb : 2≤b) : repunit b n=(b^n-1)/(b-1) := by
  apply Nat.eq_div_of_mul_eq_left (by omega)
  have h := geometric_identity b n (by omega)
  rw [mul_comm] at h
  omega

def fastMask (w n g : ℕ) : ℕ := g*(((1 <<< (w*n))-1)/((1 <<< w)-1))
theorem fastMask_eq (w n g : ℕ) (hw : 0<w) : fastMask w n g=mask w n g := by
  have hb : 2≤2^w := by
    have h := Nat.one_lt_pow (show w≠0 by omega) (show 1<2 by omega)
    omega
  simp only [fastMask,mask,Nat.shiftLeft_eq,one_mul,pow_mul]
  rw [← repunit_closed (2^w) n hb]

theorem limb_shiftRight (w x i stride : ℕ) :
    limb w (x >>> (w*stride)) i=limb w x (i+stride) := by
  unfold limb
  rw [← Nat.shiftRight_add]
  congr 2
  ring
end ThomsonNine.PackedRadix
