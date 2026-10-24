import ThomsonNine.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Exact interval layer for the n=10 D4d candidate

This file formalizes only the rational parameter interval and the monotone map
`h = (1 - t^2) / (1 + t^2)`.  It does not assert that the interval contains a
global Thomson minimizer, and it does not provide a ten-particle lower bound.
The interval endpoints are copied from the exact root-isolation artifact.
-/

namespace ThomsonTen

open ThomsonNine.Interval

def tLo : ℚ := 63701661910807 / 100000000000000
def tHi : ℚ := 63701661910808 / 100000000000000

def hLo : ℚ :=
  92845285465642394785199799 / 219654714534357605214800201
def hHi : ℚ :=
  5942098269801240669576608751 / 14057901730198759330423391249

def tInterval : RatInterval :=
  ⟨tLo, tHi, by norm_num [tLo, tHi]⟩

def hInterval : RatInterval :=
  ⟨hLo, hHi, by norm_num [hLo, hHi]⟩

theorem t_interval_positive : 0 < (tLo : ℝ) ∧ (tHi : ℝ) < 1 := by
  norm_num [tLo, tHi]

theorem h_interval_inside_unit : 0 < (hLo : ℝ) ∧ (hHi : ℝ) < 1 := by
  norm_num [hLo, hHi]

theorem h_map_bounds {t : ℝ}
    (htLo : (tLo : ℝ) ≤ t) (htHi : t ≤ (tHi : ℝ)) :
    (hLo : ℝ) ≤ (1 - t ^ 2) / (1 + t ^ 2) ∧
      (1 - t ^ 2) / (1 + t ^ 2) ≤ (hHi : ℝ) := by
  have htLo0 : 0 < (tLo : ℝ) := by norm_num [tLo]
  have htHi1 : (tHi : ℝ) < 1 := by norm_num [tHi]
  have ht0 : 0 < t := lt_of_lt_of_le htLo0 htLo
  have hden : 0 < 1 + t ^ 2 := by positivity
  have hsqLo : (tLo : ℝ) ^ 2 ≤ t ^ 2 := by
    simpa [pow_two] using
      (mul_self_le_mul_self (le_of_lt htLo0) htLo)
  have hsqHi : t ^ 2 ≤ (tHi : ℝ) ^ 2 := by
    simpa [pow_two] using
      (mul_self_le_mul_self (le_of_lt ht0) htHi)
  have hLo0 : 0 < (hLo : ℝ) := by norm_num [hLo]
  have hHi0 : 0 < (hHi : ℝ) := by norm_num [hHi]
  have hLoEq :
      (hLo : ℝ) * (1 + (tHi : ℝ) ^ 2) = 1 - (tHi : ℝ) ^ 2 := by
    norm_num [hLo, tHi]
  have hHiEq :
      1 - (tLo : ℝ) ^ 2 = (hHi : ℝ) * (1 + (tLo : ℝ) ^ 2) := by
    norm_num [hHi, tLo]
  norm_num [tLo, tHi] at hsqLo hsqHi
  constructor
  · apply (le_div_iff₀ hden).2
    norm_num [hLo, tHi] at hLoEq ⊢
    linarith
  · apply (div_le_iff₀ hden).2
    norm_num [hHi, tLo] at hHiEq ⊢
    linarith

theorem h_map_mem_interval {t : ℝ}
    (ht : tInterval.mem t) :
    hInterval.mem ((1 - t ^ 2) / (1 + t ^ 2)) :=
  h_map_bounds ht.1 ht.2

theorem exists_eq_zero_of_continuousOn_Icc {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b))
    (ha : f a ≤ 0) (hb : 0 ≤ f b) :
    ∃ x ∈ Set.Icc a b, f x = 0 := by
  have hzero : (0 : ℝ) ∈ Set.Icc (f a) (f b) := ⟨ha, hb⟩
  rcases intermediate_value_Icc hab hf hzero with ⟨x, hx, hfx⟩
  exact ⟨x, hx, hfx⟩

noncomputable def d4dStationarity (t : ℝ) : ℝ :=
    4 * ((t + 1) / Real.sqrt (1 + t ^ 2) -
      Real.sqrt (1 + t ^ 2) / t ^ 2)
      + (1 - 1 / t ^ 2) * (1 + 2 * Real.sqrt 2)
      + 4 * (2 * t / Real.sqrt (t ^ 4 + Real.sqrt 2 * t ^ 2 + 1)
        - (1 + t ^ 2) * t * (2 * t ^ 2 + Real.sqrt 2) /
            Real.sqrt (t ^ 4 + Real.sqrt 2 * t ^ 2 + 1) ^ 3
        + 2 * t / Real.sqrt (t ^ 4 - Real.sqrt 2 * t ^ 2 + 1)
        - (1 + t ^ 2) * t * (2 * t ^ 2 - Real.sqrt 2) /
            Real.sqrt (t ^ 4 - Real.sqrt 2 * t ^ 2 + 1) ^ 3)

theorem exists_d4d_stationary_root_of_signs {a b : ℝ}
    (hab : a ≤ b)
    (hcont : ContinuousOn d4dStationarity (Set.Icc a b))
    (ha : d4dStationarity a ≤ 0) (hb : 0 ≤ d4dStationarity b) :
    ∃ x ∈ Set.Icc a b, d4dStationarity x = 0 :=
  exists_eq_zero_of_continuousOn_Icc hab hcont ha hb

theorem d4dStationarity_continuousOn_tInterval :
    ContinuousOn d4dStationarity
      (Set.Icc (tLo : ℝ) (tHi : ℝ)) := by
  intro t ht
  have htlo : (tLo : ℝ) ≤ t := ht.1
  have ht0 : t ≠ 0 := by
    have : 0 < t := lt_of_lt_of_le (by norm_num [tLo]) htlo
    linarith
  have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht0
  have ht1 : t < 1 := lt_of_le_of_lt ht.2 (by norm_num [tHi])
  have hs2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hradA : 0 < t ^ 4 + Real.sqrt 2 * t ^ 2 + 1 := by
    positivity
  have hradB : 0 < t ^ 4 - Real.sqrt 2 * t ^ 2 + 1 := by
    nlinarith [sq_nonneg (t ^ 2 - Real.sqrt 2 / 2)]
  have hs1 : Real.sqrt (1 + t ^ 2) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hsA : Real.sqrt (t ^ 4 + Real.sqrt 2 * t ^ 2 + 1) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.mpr hradA)
  have hsB : Real.sqrt (t ^ 4 - Real.sqrt 2 * t ^ 2 + 1) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.mpr hradB)
  unfold d4dStationarity
  fun_prop (disch := aesop)

end ThomsonTen
