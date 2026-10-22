import PackedTensor.AffineRows
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.BigOperators.Field

noncomputable section
namespace ThomsonNine.PackedTensor
open scoped BigOperators

def weight (level pos j : ℕ) : ℚ :=
  if pos≤j ∧ j≤pos+level then (level.choose (j-pos) : ℚ)/2^level else 0

def rowSpec (d : ℕ) : Prop :=
  (∀ pos j : Fin d, weight 0 pos.val j.val=if j=pos then 1 else 0) ∧
  (∀ level pos j : Fin d, level.val+pos.val+1<d →
    weight (level.val+1) pos.val j.val=
      (weight level.val pos.val j.val+weight level.val (pos.val+1) j.val)/2)

instance (d : ℕ) : Decidable (rowSpec d) := inferInstanceAs (Decidable (_ ∧ _))

theorem realRow_matrix (d : ℕ) (h : rowSpec d) (parent : ℕ → ℝ) :
    ∀ level pos : ℕ, level+pos<d → realRow parent level pos=
      ∑ j : Fin d, (weight level pos j.val : ℝ)*parent j.val := by
  intro level
  induction level with
  | zero =>
    intro pos hp
    have hs (j : Fin d) := h.1 ⟨pos,by omega⟩ j
    simp [realRow,hs,apply_ite]
  | succ level ih =>
    intro pos hp
    rw [realRow,ih pos (by omega),ih (pos+1) (by omega)]
    rw [← Finset.sum_add_distrib,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    have hs := h.2 ⟨level,by omega⟩ ⟨pos,by omega⟩ j (show level+pos+1<d by omega)
    rw [hs]
    push_cast
    ring
end ThomsonNine.PackedTensor
