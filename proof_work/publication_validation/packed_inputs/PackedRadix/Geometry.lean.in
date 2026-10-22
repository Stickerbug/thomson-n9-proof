import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace ThomsonNine.PackedRadix
open scoped BigOperators
def repunit (b n : ℕ) : ℕ := ∑ j∈Finset.range n, b^j
def mask (w n g : ℕ) : ℕ := g*repunit (2^w) n
def digit (b x i : ℕ) : ℕ := x/b^i%b
def limb (w x i : ℕ) : ℕ := (x >>> (w*i))%2^w

theorem repunit_zero (b : ℕ) : repunit b 0=0 := by simp [repunit]
theorem repunit_succ (b n : ℕ) : repunit b (n+1)=repunit b n+b^n := by
  simp only [repunit,Finset.sum_range_succ]
theorem repunit_add (b n k : ℕ) : repunit b (n+k)=repunit b n+b^n*repunit b k := by
  induction k with
  | zero => simp [repunit]
  | succ k ih => rw [Nat.add_succ,repunit_succ,ih,repunit_succ,pow_add];ring
theorem repunit_cons (b n : ℕ) : repunit b (n+1)=1+b*repunit b n := by
  have h := repunit_add b 1 n
  simpa [repunit,Nat.add_comm] using h

theorem geometric_identity (b n : ℕ) (hb : 1≤b) : (b-1)*repunit b n+1=b^n := by
  induction n with
  | zero => simp [repunit]
  | succ n ih =>
    rw [repunit_succ,pow_succ]
    have he : b-1+1=b := Nat.sub_add_cancel hb
    have hp := congrArg (fun k : ℕ => k*b^n) he
    nlinarith

theorem mask_bound (b n g : ℕ) (hb : 1≤b) (hg : g<b) : g*repunit b n<b^n := by
  have hmul := Nat.mul_le_mul_right (repunit b n) (show g≤b-1 by omega)
  have hgeom := geometric_identity b n hb
  omega

theorem mask_prefix (b n i g : ℕ) (hb : 1≤b) (hi : i≤n) (hg : g<b) :
    (g*repunit b n)%b^i=g*repunit b i := by
  have hn : n=i+(n-i) := by omega
  have he := repunit_add b i (n-i)
  rw [← hn] at he
  calc
    (g*repunit b n)%b^i=(g*repunit b i+b^i*(g*repunit b (n-i)))%b^i := by
      congr 1
      rw [he]
      ring
    _ = g*repunit b i := by rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (mask_bound b i g hb hg)]

theorem digit_mask (b n i g : ℕ) (hb : 1≤b) (hi : i<n) (hg : g<b) :
    digit b (g*repunit b n) i=g := by
  let k := n-(i+1)
  have hn : n=i+(k+1) := by dsimp [k];omega
  have he : g*repunit b n=g*repunit b i+b^i*(g+b*(g*repunit b k)) := by
    rw [hn,repunit_add,repunit_cons]
    ring
  have hm : 0<b^i := pow_pos (by omega) _
  rw [digit,he,Nat.add_mul_div_left _ _ hm,Nat.div_eq_of_lt (mask_bound b i g hb hg),zero_add,
    Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hg]

theorem limb_eq_digit (w x i : ℕ) : limb w x i=digit (2^w) x i := by
  simp only [limb,digit,Nat.shiftRight_eq_div_pow,pow_mul]

theorem limb_and (w x y i : ℕ) : limb w (x &&& y) i=limb w x i &&& limb w y i := by
  simp only [limb,Nat.shiftRight_and_distrib,Nat.and_mod_two_pow]

theorem limb_mask (w n i g : ℕ) (hi : i<n) (hg : g<2^w) : limb w (mask w n g) i=g := by
  rw [limb_eq_digit,mask]
  exact digit_mask (2^w) n i g (Nat.one_le_pow w 2 (by omega)) hi hg

theorem masked_limb_le (w n g x i : ℕ) (hi : i<n) (hg : g<2^w)
    (hx : x &&& mask w n g=x) : limb w x i≤g := by
  have he := congrArg (fun a => limb w a i) hx
  rw [limb_and,limb_mask w n i g hi hg] at he
  rw [← he]
  exact Nat.and_le_right

theorem masked_prefix_le (w n i g x : ℕ) (hi : i≤n) (hg : g<2^w)
    (hx : x &&& mask w n g=x) : x%(2^w)^i≤g*repunit (2^w) i := by
  have he := congrArg (fun a => a%2^(w*i)) hx
  rw [Nat.and_mod_two_pow] at he
  have hm : (mask w n g)%2^(w*i)=g*repunit (2^w) i := by
    rw [pow_mul,mask]
    exact mask_prefix (2^w) n i g (Nat.one_le_pow w 2 (by omega)) hi hg
  rw [hm,pow_mul] at he
  rw [← he]
  exact Nat.and_le_right
end ThomsonNine.PackedRadix
