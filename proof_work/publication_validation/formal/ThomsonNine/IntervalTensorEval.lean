/-
Whole-tensor interval evaluation.

`evalTensor` evaluates a ternary Bernstein tensor with interval coefficients over
three parameter intervals, and `evalTensor_sound` proves that the resulting
interval encloses the tensor value at every parameter triple in those intervals.
-/
import ThomsonNine.IntervalSum
import ThomsonNine.LeafSemantics

namespace ThomsonNine
namespace Interval
namespace RatInterval

open ThomsonNine.Semantics (tensor bernstein)

/-- Extensionality for interval certificates (the validity proof is irrelevant). -/
@[ext] theorem ext' {I J : RatInterval} (hlo : I.lo = J.lo) (hhi : I.hi = J.hi) : I = J := by
  cases I with
  | mk lo hi h =>
    cases J with
    | mk lo' hi' h' =>
      simp only at hlo hhi
      subst hlo
      subst hhi
      rfl

/-- Scalar multiplication of an interval by a natural number. -/
def nsmulI (n : ℕ) (I : RatInterval) : RatInterval :=
  ⟨(n : ℚ) * I.lo, (n : ℚ) * I.hi, by
    have hn : (0 : ℚ) ≤ (n : ℚ) := by exact_mod_cast Nat.zero_le n
    exact mul_le_mul_of_nonneg_left I.h hn⟩

instance instAddCommMonoid : AddCommMonoid RatInterval where
  add := add
  add_assoc := by
    intro a b c
    apply ext'
    · show ((a.lo + b.lo) + c.lo) = (a.lo + (b.lo + c.lo)); ring
    · show ((a.hi + b.hi) + c.hi) = (a.hi + (b.hi + c.hi)); ring
  zero := const 0
  zero_add := by
    intro a
    apply ext'
    · show ((0 : ℚ) + a.lo) = a.lo; ring
    · show ((0 : ℚ) + a.hi) = a.hi; ring
  add_zero := by
    intro a
    apply ext'
    · show (a.lo + (0 : ℚ)) = a.lo; ring
    · show (a.hi + (0 : ℚ)) = a.hi; ring
  nsmul := nsmulI
  nsmul_zero := by
    intro I
    apply ext'
    · show ((0 : ℚ) * I.lo) = (0 : ℚ); ring
    · show ((0 : ℚ) * I.hi) = (0 : ℚ); ring
  nsmul_succ := by
    intro n I
    apply ext'
    · show (((n + 1 : ℕ)) : ℚ) * I.lo = (n : ℚ) * I.lo + I.lo; push_cast; ring
    · show (((n + 1 : ℕ)) : ℚ) * I.hi = (n : ℚ) * I.hi + I.hi; push_cast; ring
  add_comm := by
    intro a b
    apply ext'
    · show (a.lo + b.lo) = (b.lo + a.lo); ring
    · show (a.hi + b.hi) = (b.hi + a.hi); ring

/-- Enclosure of a finite sum of enclosures. -/
theorem mem_sum {ι : Type*} (s : Finset ι) (f : ι → RatInterval) (g : ι → ℝ)
    (h : ∀ i ∈ s, (f i).mem (g i)) :
    (∑ i ∈ s, f i).mem (∑ i ∈ s, g i) := by
  classical
  revert f g
  induction s using Finset.induction with
  | empty =>
      intro f g h
      simp only [Finset.sum_empty]
      change (const (0 : ℚ)).mem (0 : ℝ)
      constructor <;> simp [const]
  | insert a s ha ih =>
      intro f g h
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact mem_add (h a (Finset.mem_insert_self a s))
        (ih f g (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- Interval evaluation of a ternary Bernstein tensor on a box. -/
noncomputable def evalTensor (n : ℕ)
    (C : Fin (n+1) → Fin (n+1) → Fin (n+1) → RatInterval)
    (Iu Iv It : RatInterval) (hu0 : 0 ≤ Iu.lo) (hu1 : Iu.hi ≤ 1)
    (hv0 : 0 ≤ Iv.lo) (hv1 : Iv.hi ≤ 1) (ht0 : 0 ≤ It.lo) (ht1 : It.hi ≤ 1) : RatInterval :=
  ∑ i : Fin (n+1), ∑ j : Fin (n+1), ∑ k : Fin (n+1),
    let Bu := bernInterval n i.val Iu hu0 hu1
    let Bv := bernInterval n j.val Iv hv0 hv1
    let Bt := bernInterval n k.val It ht0 ht1
    mulMixed (mulMixed (mulMixed (C i j k) Bu
      (bernInterval_lo_nonneg n i.val Iu hu0 hu1)) Bv
      (bernInterval_lo_nonneg n j.val Iv hv0 hv1)) Bt
      (bernInterval_lo_nonneg n k.val It ht0 ht1)

/-- Soundness of the whole-tensor interval evaluation. -/
theorem evalTensor_sound (n : ℕ)
    (C : Fin (n+1) → Fin (n+1) → Fin (n+1) → RatInterval)
    (c : Fin (n+1) → Fin (n+1) → Fin (n+1) → ℝ)
    (hC : ∀ i j k, (C i j k).mem (c i j k))
    (Iu Iv It : RatInterval) (hu0 : 0 ≤ Iu.lo) (hu1 : Iu.hi ≤ 1)
    (hv0 : 0 ≤ Iv.lo) (hv1 : Iv.hi ≤ 1) (ht0 : 0 ≤ It.lo) (ht1 : It.hi ≤ 1)
    {u v t : ℝ} (hu : Iu.mem u) (hv : Iv.mem v) (ht : It.mem t) :
    (evalTensor n C Iu Iv It hu0 hu1 hv0 hv1 ht0 ht1).mem (tensor n c u v t) := by
  unfold evalTensor tensor
  refine mem_sum Finset.univ _ _ ?_
  intro i _
  refine mem_sum Finset.univ _ _ ?_
  intro j _
  refine mem_sum Finset.univ _ _ ?_
  intro k _
  show (mulMixed (mulMixed (mulMixed (C i j k)
      (bernInterval n i.val Iu hu0 hu1) (bernInterval_lo_nonneg n i.val Iu hu0 hu1))
      (bernInterval n j.val Iv hv0 hv1) (bernInterval_lo_nonneg n j.val Iv hv0 hv1))
      (bernInterval n k.val It ht0 ht1) (bernInterval_lo_nonneg n k.val It ht0 ht1)).mem
    (c i j k * bernstein n i.val u * bernstein n j.val v * bernstein n k.val t)
  exact mem_mulMixed (bernInterval_lo_nonneg n k.val It ht0 ht1)
    (mem_mulMixed3 (bernInterval_lo_nonneg n i.val Iu hu0 hu1)
      (bernInterval_lo_nonneg n j.val Iv hv0 hv1) (hC i j k)
      (mem_bernInterval n i.val Iu hu0 hu1 hu)
      (mem_bernInterval n j.val Iv hv0 hv1 hv))
    (mem_bernInterval n k.val It ht0 ht1 ht)

end RatInterval
end Interval
end ThomsonNine
