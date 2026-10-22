import Algebra.FiniteCollectorZero
import Mathlib.Algebra.BigOperators.Fin

noncomputable section
namespace ThomsonNine.FiniteCollector
open scoped BigOperators

theorem bounded_offset (P : ℕ → Prop) (lo count : ℕ) (h : ∀ i : Fin count, P (lo+i.val))
    (id : ℕ) (hl : lo ≤ id) (hr : id < lo+count) : P id := by
  have hi : id-lo<count := by omega
  have he : lo+(id-lo)=id := by omega
  simpa only [he] using h ⟨id-lo,hi⟩

theorem range_sum_eq_fin (n : ℕ) (f : ℕ → ℝ) :
    ((List.range n).map f).sum=∑ i : Fin n, f i.val := by
  have hNat : ((List.range n).map f).sum=∑ j∈Finset.range n, f j := by
    simpa only [List.toFinset_range] using (List.sum_toFinset f (show (List.range n).Nodup from List.nodup_range)).symm
  exact hNat.trans (Fin.sum_univ_eq_sum_range f n).symm
end ThomsonNine.FiniteCollector
