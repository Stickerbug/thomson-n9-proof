import PackedTensor.TensorModel

namespace ThomsonNine.PackedRadix
open ThomsonNine.PackedTensor

def uniHalf (d g : ℕ) (right : Bool) (packet : ℕ) : ℕ :=
  let rows := makeRows d g 1 d packet
  (List.finRange d).foldl (fun out i =>
    let value := if right then limb 128 (rowAt rows (d-1-i.val)) i.val else limb 128 (rowAt rows i.val) 0
    out ||| (value <<< (128*i.val))) 0

def uniHalfOK (d g : ℕ) (right : Bool) (packet : ℕ) : Bool :=
  let rows := makeRows d g 1 d packet
  rowsOK d d g 1 packet rows && decide (
    (∀ i : Fin d, limb 128 (uniHalf d g right packet) i.val=
      if right then limb 128 (rowAt rows (d-1-i.val)) i.val else limb 128 (rowAt rows i.val) 0) ∧
    uniHalf d g right packet &&& fastMask 128 d g=uniHalf d g right packet)

noncomputable def uniValue (n offset scale packet : ℕ) (s : ℝ) : ℝ :=
  curve n (fun i => decode offset scale packet i.val) s

theorem curve_mono (n : ℕ) (b c : Fin (n+1) → ℝ) (hbc : ∀ i, b i≤c i)
    (s : ℝ) (hs : 0≤s ∧ s≤1) : curve n b s≤curve n c s := by
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hbc i)
    (Semantics.bernstein_nonneg n i.val hs.1 hs.2))

theorem uniHalf_lower (n g offset scale : ℕ) (hr : rowSpec (n+1)) (hb : basisSpec n)
    (side : Bool) (packet : ℕ) (hg : 2*g+1<2^128)
    (h : uniHalfOK (n+1) g side packet=true) (hscale : (0 : ℝ)<scale)
    (s : ℝ) (hs : 0≤s ∧ s≤1) :
    uniValue n offset scale (uniHalf (n+1) g side packet) s≤
      uniValue n offset scale packet ((if side then 1+s else s)/2) := by
  have hp := Bool.and_eq_true_iff.mp h
  have hq : (∀ i : Fin (n+1), limb 128 (uniHalf (n+1) g side packet) i.val=
      if side then limb 128 (rowAt (makeRows (n+1) g 1 (n+1) packet) (n+1-1-i.val)) i.val
      else limb 128 (rowAt (makeRows (n+1) g 1 (n+1) packet) i.val) 0) ∧
      uniHalf (n+1) g side packet &&& fastMask 128 (n+1) g=uniHalf (n+1) g side packet :=
    of_decide_eq_true hp.2
  let parent := fun j => decode offset scale packet j
  have hrows := rows_bound (n+1) (n+1) g 1 packet offset scale _ hg hp.1 hscale 0 parent
    (fun j hj => by simpa using hj) (fun j _ => by simp [parent])
  unfold uniValue
  have hc (i : Fin (n+1)) : decode offset scale (uniHalf (n+1) g side packet) i.val≤
      if side then realRow parent (n-i.val) i.val else realRow parent i.val 0 := by
    cases side
    · have hh := hrows i.val 0 (by omega)
      simpa only [decode,hq.1 i,Bool.false_eq_true,ite_false,Nat.mul_zero,Nat.add_zero] using hh
    · have hh := hrows (n-i.val) i.val (by omega)
      simpa only [decode,hq.1 i,ite_true,Nat.add_sub_cancel,Nat.zero_add,one_mul] using hh
  exact (curve_mono n _ _ hc s hs).trans_eq (curve_half n hr hb parent side s)
end ThomsonNine.PackedRadix
