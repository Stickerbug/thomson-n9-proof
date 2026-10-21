import ThomsonNine.EnergyGradient

open Finset

example (A : Fin 9 → Fin 9 → ℝ) :
    (∑ i : Fin 9, ∑ j ∈ Finset.Iio i, A i j) = ∑ i : Fin 9, ∑ j ∈ Finset.Ioi i, A j i := by
  simp only [← Finset.filter_gt_eq_Iio, ← Finset.filter_lt_eq_Ioi]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
