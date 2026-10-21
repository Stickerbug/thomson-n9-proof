/-
A certified rational upper bound on the candidate family energy.

The frozen numerical value is `E* ≈ 25.75998653126983156407570227376049402864`.
Here we prove the much coarser but fully checked bound
`familyEnergy (7/10) < 26`, and hence, using the strict global minimality of
the family energy at its stationary point `r*`, that the true minimum
`familyEnergy r*` and the energy of the actual candidate configuration
`candidate r*` are both `< 26`.

All square-root bounds are rational and checked by `norm_num`; no `sorry` or
`axiom` is used.
-/
import ThomsonNine.Minimum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open scoped BigOperators

namespace ThomsonNine.Family

/-- `√3 < 1.733`. -/
lemma sqrt3_lt_1733 : Real.sqrt 3 < 1.733 := by
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1.733)]
  norm_num

/-- `0.714 < √(1 - (7/10)^2)`. -/
lemma sqrt_051_gt : (0.714 : ℝ) < Real.sqrt (1 - (7 / 10) ^ 2) := by
  rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 0.714)]
  norm_num

/-- `1.87 < √(4 - (7/10)^2)`. -/
lemma sqrt_351_gt : (1.87 : ℝ) < Real.sqrt (4 - (7 / 10) ^ 2) := by
  rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1.87)]
  norm_num

/-- `1.14 < √(2 - 7/10)`. -/
lemma sqrt_13_gt : (1.14 : ℝ) < Real.sqrt (2 - 7 / 10) := by
  rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1.14)]
  norm_num

/-- `1.84 < √(2 + 2*(7/10))`. -/
lemma sqrt_34_gt : (1.84 : ℝ) < Real.sqrt (2 + 2 * (7 / 10)) := by
  rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1.84)]
  norm_num

/-- `familyEnergy (7/10) < 26`. -/
theorem familyEnergy_seven_tenths_lt_26 : familyEnergy (7 / 10) < 26 := by
  unfold familyEnergy
  have t1 : Real.sqrt 3 < 1.733 := sqrt3_lt_1733
  have t2 : 2 * Real.sqrt 3 / (7 / 10) < 4.952 := by
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 7 / 10)]
    nlinarith [t1]
  have t3 : 3 / (2 * Real.sqrt (1 - (7 / 10) ^ 2)) < 2.101 := by
    have hd : (0.714 : ℝ) < Real.sqrt (1 - (7 / 10) ^ 2) := sqrt_051_gt
    have harg : (0 : ℝ) < 1 - (7 / 10) ^ 2 := by norm_num
    have hpos : (0 : ℝ) < 2 * Real.sqrt (1 - (7 / 10) ^ 2) := by
      have := Real.sqrt_pos.mpr harg
      positivity
    rw [div_lt_iff₀ hpos]
    nlinarith [hd]
  have t4 : 6 / Real.sqrt (4 - (7 / 10) ^ 2) < 3.209 := by
    have hd : (1.87 : ℝ) < Real.sqrt (4 - (7 / 10) ^ 2) := sqrt_351_gt
    have harg : (0 : ℝ) < 4 - (7 / 10) ^ 2 := by norm_num
    have hpos : (0 : ℝ) < Real.sqrt (4 - (7 / 10) ^ 2) := Real.sqrt_pos.mpr harg
    rw [div_lt_iff₀ hpos]
    nlinarith [hd]
  have t5 : 12 / Real.sqrt (2 - 7 / 10) < 10.527 := by
    have hd : (1.14 : ℝ) < Real.sqrt (2 - 7 / 10) := sqrt_13_gt
    have harg : (0 : ℝ) < 2 - 7 / 10 := by norm_num
    have hpos : (0 : ℝ) < Real.sqrt (2 - 7 / 10) := Real.sqrt_pos.mpr harg
    rw [div_lt_iff₀ hpos]
    nlinarith [hd]
  have t6 : 6 / Real.sqrt (2 + 2 * (7 / 10)) < 3.261 := by
    have hd : (1.84 : ℝ) < Real.sqrt (2 + 2 * (7 / 10)) := sqrt_34_gt
    have harg : (0 : ℝ) < 2 + 2 * (7 / 10) := by norm_num
    have hpos : (0 : ℝ) < Real.sqrt (2 + 2 * (7 / 10)) := Real.sqrt_pos.mpr harg
    rw [div_lt_iff₀ hpos]
    nlinarith [hd]
  nlinarith [t1, t2, t3, t4, t5, t6]

/-- The true family minimum is `< 26`. -/
theorem familyEnergy_stationary_lt_26 :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ familyEnergyDeriv r = 0 ∧ familyEnergy r < 26 := by
  obtain ⟨r, ⟨hr, hr1, hz, hmin⟩, _⟩ := exists_unique_familyEnergy_min
  refine ⟨r, hr, hr1, hz, ?_⟩
  rcases eq_or_ne r (7 / 10) with h | h
  · rw [h]; exact familyEnergy_seven_tenths_lt_26
  · exact lt_trans
      (hmin (7 / 10) (by norm_num) (by norm_num) h.symm)
      familyEnergy_seven_tenths_lt_26

/-- The actual candidate configuration has energy `< 26`. -/
theorem exists_candidate_energy_lt_26 :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ familyEnergyDeriv r = 0 ∧
      energy (candidate r) < 26 := by
  obtain ⟨r, hr, hr1, hz, hlt⟩ := familyEnergy_stationary_lt_26
  refine ⟨r, hr, hr1, hz, ?_⟩
  rw [energy_candidate r hr hr1]
  exact hlt

end ThomsonNine.Family
