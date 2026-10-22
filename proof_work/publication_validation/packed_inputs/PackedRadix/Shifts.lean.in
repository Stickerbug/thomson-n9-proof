import PackedRadix.FastMasks

namespace ThomsonNine.PackedRadix
theorem limb_shiftLeft (w x i stride : ℕ) :
    limb w (x <<< (w*stride)) (i+stride)=limb w x i := by
  simp only [limb,Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow,Nat.mul_add,pow_add]
  rw [Nat.mul_div_mul_right _ _ (pow_pos (by omega) _)]
end ThomsonNine.PackedRadix
