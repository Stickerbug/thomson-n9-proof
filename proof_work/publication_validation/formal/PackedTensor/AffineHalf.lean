import PackedTensor.AffineRows

noncomputable section
namespace ThomsonNine.PackedTensor
open ThomsonNine.PackedRadix

def line {d : ℕ} [NeZero d] (coeff : CubeIndex d → ℝ) (axis : Fin 3)
    (p : CubeIndex d) (j : ℕ) : ℝ := coeff (replace axis p (Fin.ofNat d j))

theorem half_left_bound {d : ℕ} [NeZero d] (n g offset scale : ℕ)
    (planes : Fin 3 → Fin d → ℕ) (hplanes : PlaneSpec planes) (axis : Fin 3) (x : ℕ)
    (hg : 2*g+1<2^128) (h : halfOK n g planes axis false x=true)
    (hs : (0 : ℝ)<scale) (hn : d*d*d≤n) (coeff : CubeIndex d → ℝ)
    (hbase : ∀ p, decode offset scale x (flat p)≤coeff p) (p : CubeIndex d) :
    decode offset scale (half n g planes axis false x) (flat p)≤
      realRow (line coeff axis p) (coord axis p).val 0 := by
  have hi (j : ℕ) (hj : j<d) : zeroIndex axis p+stride d axis*j<n := by
    have hf := flat_lt (replace axis p ⟨j,hj⟩)
    rw [flat_replace] at hf
    exact lt_of_lt_of_le hf hn
  have hb (j : ℕ) (hj : j<d) :
      decode offset scale x (zeroIndex axis p+stride d axis*j)≤line coeff axis p j := by
    have he : Fin.ofNat d j=⟨j,hj⟩ := by apply Fin.ext;exact Nat.mod_eq_of_lt hj
    simpa only [line,he,flat_replace] using hbase (replace axis p ⟨j,hj⟩)
  have hr := rows_bound d n g (stride d axis) x offset scale _ hg
    (half_checks n g planes axis false x h).1 hs (zeroIndex axis p) (line coeff axis p) hi hb
    (coord axis p).val 0 (by omega)
  simpa only [decode,half_left_limb n g planes hplanes axis x h p,Nat.mul_zero,Nat.add_zero] using hr

theorem half_right_bound {d : ℕ} [NeZero d] (n g offset scale : ℕ)
    (planes : Fin 3 → Fin d → ℕ) (hplanes : PlaneSpec planes) (axis : Fin 3) (x : ℕ)
    (hg : 2*g+1<2^128) (h : halfOK n g planes axis true x=true)
    (hs : (0 : ℝ)<scale) (hn : d*d*d≤n) (coeff : CubeIndex d → ℝ)
    (hbase : ∀ p, decode offset scale x (flat p)≤coeff p) (p : CubeIndex d) :
    decode offset scale (half n g planes axis true x) (flat p)≤
      realRow (line coeff axis p) (d-1-(coord axis p).val) (coord axis p).val := by
  have hi (j : ℕ) (hj : j<d) : zeroIndex axis p+stride d axis*j<n := by
    have hf := flat_lt (replace axis p ⟨j,hj⟩)
    rw [flat_replace] at hf
    exact lt_of_lt_of_le hf hn
  have hb (j : ℕ) (hj : j<d) :
      decode offset scale x (zeroIndex axis p+stride d axis*j)≤line coeff axis p j := by
    have he : Fin.ofNat d j=⟨j,hj⟩ := by apply Fin.ext;exact Nat.mod_eq_of_lt hj
    simpa only [line,he,flat_replace] using hbase (replace axis p ⟨j,hj⟩)
  have hc := (coord axis p).isLt
  have hr := rows_bound d n g (stride d axis) x offset scale _ hg
    (half_checks n g planes axis true x h).1 hs (zeroIndex axis p) (line coeff axis p) hi hb
    (d-1-(coord axis p).val) (coord axis p).val (by omega)
  simpa only [decode,half_right_limb n g planes hplanes axis x h p,← flat_decompose axis p] using hr
end ThomsonNine.PackedTensor
