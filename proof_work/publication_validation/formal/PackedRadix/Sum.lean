import PackedRadix.Checker
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ThomsonNine.PackedRadix
open scoped BigOperators

theorem div_finset_sum_no_carry {α : Type*} (s : Finset α) (f : α → ℕ) (m : ℕ)
    (hm : 0<m) (h : (∑ a∈s, f a % m)<m) :
    (∑ a∈s, f a)/m=∑ a∈s, f a/m := by
  have he : (∑ a∈s, f a)=(∑ a∈s, f a%m)+m*(∑ a∈s, f a/m) := by
    rw [Finset.mul_sum,← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun a _ => (Nat.mod_add_div (f a) m).symm)
  rw [he,Nat.add_mul_div_left _ _ hm,Nat.div_eq_of_lt h,zero_add]

theorem sum_lanes (w n g : ℕ) (k : ℕ) (x : Fin k → ℕ)
    (hg : k*g<2^w) (hx : ∀ a, x a &&& mask w n g=x a) (i : ℕ) (hi : i<n) :
    limb w (∑ a, x a) i=∑ a, limb w (x a) i := by
  by_cases hk : k=0
  · subst k;simp [limb]
  have hg' : g<2^w := lt_of_le_of_lt (Nat.le_mul_of_pos_left g (by omega)) hg
  let b := 2^w
  let R := repunit b i
  have hb : 1≤b := Nat.one_le_pow _ _ (by omega)
  have hm : 0<b^i := pow_pos (by omega) _
  have hprefix : (∑ a, x a % b^i)<b^i := by
    calc
      (∑ a, x a % b^i)≤∑ _a : Fin k, g*R :=
        Finset.sum_le_sum (fun a _ => masked_prefix_le w n i g (x a) (by omega) hg' (hx a))
      _ = (k*g)*R := by simp;ring
      _ < b^i := mask_bound b i (k*g) hb hg
  have hlim : (∑ a, limb w (x a) i)<b := by
    calc
      (∑ a, limb w (x a) i)≤∑ _a : Fin k, g :=
        Finset.sum_le_sum (fun a _ => masked_limb_le w n g (x a) i hi hg' (hx a))
      _ = k*g := by simp
      _ < b := hg
  simp only [limb_eq_digit,digit]
  rw [div_finset_sum_no_carry Finset.univ x (b^i) hm hprefix]
  rw [Finset.sum_nat_mod]
  simp only [limb_eq_digit,digit] at hlim
  exact Nat.mod_eq_of_lt hlim

def positiveSumOK (w n g bias : ℕ) (k : ℕ) (x : Fin k → ℕ) : Bool :=
  decide ((∀ a, x a &&& fastMask w n g=x a) ∧
    (∑ a, x a) &&& fastMask w n bias=fastMask w n bias)

theorem positiveSumOK_sound (w n g bias : ℕ) (k : ℕ) (x : Fin k → ℕ)
    (hw : 0<w) (hg : k*g<2^w) (hbias : bias<2^w)
    (h : positiveSumOK w n g bias k x=true) (i : ℕ) (hi : i<n) :
    bias≤∑ a, limb w (x a) i := by
  have hp : (∀ a, x a &&& fastMask w n g=x a) ∧
      (∑ a, x a) &&& fastMask w n bias=fastMask w n bias := of_decide_eq_true h
  simp only [fastMask_eq w n g hw,fastMask_eq w n bias hw] at hp
  have he := congrArg (fun z => limb w z i) hp.2
  rw [limb_and,limb_mask w n i bias hi hbias] at he
  have hs := sum_lanes w n g k x hg hp.1 i hi
  rw [← he,← hs]
  exact Nat.and_le_left
end ThomsonNine.PackedRadix
