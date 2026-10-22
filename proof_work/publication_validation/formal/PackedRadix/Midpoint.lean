import PackedRadix.Geometry

namespace ThomsonNine.PackedRadix

theorem div_add_no_carry (x y m : ℕ) (hm : 0<m) (h : x%m+y%m<m) :
    (x+y)/m=x/m+y/m := by
  have he : x+y=(x%m+y%m)+m*(x/m+y/m) := by
    nlinarith [Nat.mod_add_div x m,Nat.mod_add_div y m]
  rw [he,Nat.add_mul_div_left _ _ hm,Nat.div_eq_of_lt h,zero_add]

theorem div_two_add_no_carry (z r m : ℕ) (hm : 0<m) (h : 2*(z%m)+r%m<m) :
    (2*z+r)/m=2*(z/m)+r/m := by
  have he : 2*z+r=(2*(z%m)+r%m)+m*(2*(z/m)+r/m) := by
    nlinarith [Nat.mod_add_div z m,Nat.mod_add_div r m]
  rw [he,Nat.add_mul_div_left _ _ hm,Nat.div_eq_of_lt h,zero_add]

theorem two_add_mod (z r b : ℕ) : (2*z+r)%b=(2*(z%b)+r%b)%b := by
  have he : 2*z+r=(2*(z%b)+r%b)+b*(2*(z/b)+r/b) := by
    nlinarith [Nat.mod_add_div z b,Nat.mod_add_div r b]
  rw [he,Nat.add_mul_mod_self_left]

/-- A whole-integer identity plus lane masks certifies every lane simultaneously. -/
theorem midpoint_lanes (w n g x y z r : ℕ) (hg : 2*g+1<2^w)
    (hx : x &&& mask w n g=x) (hy : y &&& mask w n g=y)
    (hz : z &&& mask w n g=z) (hr : r &&& mask w n 1=r)
    (heq : x+y=2*z+r) (i : ℕ) (hi : i<n) :
    limb w x i+limb w y i=2*limb w z i+limb w r i ∧ limb w r i≤1 := by
  let b := 2^w
  let R := repunit b i
  have hb : 1≤b := Nat.one_le_pow w 2 (by omega)
  have hg' : g<b := by dsimp [b];omega
  have h1 : 1<b := by dsimp [b];omega
  have hm : 0<b^i := pow_pos (by omega) _
  have hxp := masked_prefix_le w n i g x (by omega) hg' hx
  have hyp := masked_prefix_le w n i g y (by omega) hg' hy
  have hzp := masked_prefix_le w n i g z (by omega) hg' hz
  have hrp := masked_prefix_le w n i 1 r (by omega) h1 hr
  have hsumb : 2*g*R<b^i := mask_bound b i (2*g) hb (by dsimp [b];omega)
  have hsumb' : (2*g+1)*R<b^i := mask_bound b i (2*g+1) hb hg
  have hxy : x%b^i+y%b^i<b^i := by
    change x%b^i≤g*R at hxp
    change y%b^i≤g*R at hyp
    nlinarith
  have hzr : 2*(z%b^i)+r%b^i<b^i := by
    change z%b^i≤g*R at hzp
    rw [one_mul] at hrp
    change r%b^i≤R at hrp
    nlinarith
  have hxlim := masked_limb_le w n g x i hi hg' hx
  have hylim := masked_limb_le w n g y i hi hg' hy
  have hzlim := masked_limb_le w n g z i hi hg' hz
  have hrlim := masked_limb_le w n 1 r i hi h1 hr
  have hxy' : limb w x i+limb w y i<b := by dsimp [b];omega
  have hzr' : 2*limb w z i+limb w r i<b := by dsimp [b];omega
  have he := congrArg (fun a : ℕ => (a/b^i)%b) heq
  rw [div_add_no_carry x y (b^i) hm hxy,div_two_add_no_carry z r (b^i) hm hzr,
    Nat.add_mod,two_add_mod] at he
  have hlim (a : ℕ) : (a/b^i)%b=limb w a i := (limb_eq_digit w a i).symm
  simp only [hlim] at he
  rw [Nat.mod_eq_of_lt hxy',Nat.mod_eq_of_lt hzr'] at he
  exact ⟨he,hrlim⟩

theorem midpoint_floor (w n g x y z r : ℕ) (hg : 2*g+1<2^w)
    (hx : x &&& mask w n g=x) (hy : y &&& mask w n g=y)
    (hz : z &&& mask w n g=z) (hr : r &&& mask w n 1=r)
    (heq : x+y=2*z+r) (i : ℕ) (hi : i<n) :
    limb w z i=(limb w x i+limb w y i)/2 := by
  have h := midpoint_lanes w n g x y z r hg hx hy hz hr heq i hi
  omega
end ThomsonNine.PackedRadix
