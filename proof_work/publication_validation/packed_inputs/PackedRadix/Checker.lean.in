import PackedRadix.FastMasks
import PackedRadix.Midpoint

namespace ThomsonNine.PackedRadix
def average (w n g x y : ℕ) : ℕ := ((x+y) >>> 1) &&& fastMask w n g
def remainder (w n x y : ℕ) : ℕ := (x+y) &&& fastMask w n 1
def averageOK (w n g x y : ℕ) : Bool :=
  let z := average w n g x y
  let r := remainder w n x y
  decide (x &&& fastMask w n g=x ∧ y &&& fastMask w n g=y ∧
    z &&& fastMask w n g=z ∧ r &&& fastMask w n 1=r ∧ x+y=2*z+r)

theorem averageOK_sound (w n g x y : ℕ) (hw : 0<w) (hg : 2*g+1<2^w)
    (h : averageOK w n g x y=true) (i : ℕ) (hi : i<n) :
    limb w (average w n g x y) i=(limb w x i+limb w y i)/2 := by
  have hp : x &&& fastMask w n g=x ∧ y &&& fastMask w n g=y ∧
      average w n g x y &&& fastMask w n g=average w n g x y ∧
      remainder w n x y &&& fastMask w n 1=remainder w n x y ∧
      x+y=2*average w n g x y+remainder w n x y := of_decide_eq_true h
  rw [fastMask_eq w n g hw,fastMask_eq w n 1 hw] at hp
  exact midpoint_floor w n g x y (average w n g x y) (remainder w n x y) hg
    hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2 i hi

theorem averageShiftOK_sound (w n g x stride : ℕ) (hw : 0<w) (hg : 2*g+1<2^w)
    (h : averageOK w n g x (x >>> (w*stride))=true) (i : ℕ) (hi : i<n) :
    limb w (average w n g x (x >>> (w*stride))) i=(limb w x i+limb w x (i+stride))/2 := by
  rw [averageOK_sound w n g x (x >>> (w*stride)) hw hg h i hi,limb_shiftRight]
end ThomsonNine.PackedRadix
