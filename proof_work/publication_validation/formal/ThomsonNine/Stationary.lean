import ThomsonNine.Derivative
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open ThomsonNine.Family
namespace ThomsonNine.Family

lemma familyEnergyDeriv_half_neg : familyEnergyDeriv (1 / 2) < 0 := by
  have h1 : (1 : ℝ) - (1 / 2) ^ 2 = 3 / 4 := by norm_num
  have h2 : (4 : ℝ) - (1 / 2) ^ 2 = 15 / 4 := by norm_num
  have h3 : (2 : ℝ) - 1 / 2 = 3 / 2 := by norm_num
  have h4 : (2 : ℝ) + 2 * (1 / 2) = 3 := by norm_num
  have h5 : (1 / 2 : ℝ) ^ 2 = 1 / 4 := by norm_num
  simp only [familyEnergyDeriv, h1, h2, h3, h4, h5]
  have y34 : (0.86 : ℝ) < Real.sqrt (3 / 4) := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have y154 : (1.93 : ℝ) < Real.sqrt (15 / 4) := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have y32 : (1.22 : ℝ) < Real.sqrt (3 / 2) := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have x3lo : (1.7 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have x3hi : Real.sqrt 3 < 1.75 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have b1 : -2 * Real.sqrt 3 / (1 / 4 : ℝ) < -13.6 := by
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 1 / 4)]
    nlinarith
  have b2 : 3 * (1 / 2) / (2 * (Real.sqrt (3 / 4)) ^ 3) < 1.2 := by
    have hy : (0 : ℝ) < Real.sqrt (3 / 4) := by positivity
    have hc : (0.86 : ℝ) ^ 3 < (Real.sqrt (3 / 4)) ^ 3 := by
      exact pow_lt_pow_left₀ y34 (by norm_num) (by norm_num)
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (Real.sqrt (3 / 4)) ^ 3)]
    nlinarith
  have b3 : 6 * (1 / 2) / (Real.sqrt (15 / 4)) ^ 3 < 0.5 := by
    have hy : (0 : ℝ) < Real.sqrt (15 / 4) := by positivity
    have hc : (1.93 : ℝ) ^ 3 < (Real.sqrt (15 / 4)) ^ 3 := by
      exact pow_lt_pow_left₀ y154 (by norm_num) (by norm_num)
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (Real.sqrt (15 / 4)) ^ 3)]
    nlinarith
  have b4 : 6 / (Real.sqrt (3 / 2)) ^ 3 < 3.4 := by
    have hy : (0 : ℝ) < Real.sqrt (3 / 2) := by positivity
    have hc : (1.22 : ℝ) ^ 3 < (Real.sqrt (3 / 2)) ^ 3 := by
      exact pow_lt_pow_left₀ y32 (by norm_num) (by norm_num)
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (Real.sqrt (3 / 2)) ^ 3)]
    nlinarith
  have b5 : -(6 / (Real.sqrt 3) ^ 3) < -1.1 := by
    rw [← neg_div]
    have hy : (0 : ℝ) < Real.sqrt 3 := by positivity
    have hc : (Real.sqrt 3) ^ 3 < (1.75 : ℝ) ^ 3 := by
      exact pow_lt_pow_left₀ x3hi (by positivity) (by norm_num)
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (Real.sqrt 3) ^ 3)]
    nlinarith
  linarith

lemma familyEnergyDeriv_nine_tenths_pos : 0 < familyEnergyDeriv (9 / 10) := by
  have h1 : (1 : ℝ) - (9 / 10) ^ 2 = 19 / 100 := by norm_num
  have h2 : (4 : ℝ) - (9 / 10) ^ 2 = 319 / 100 := by norm_num
  have h3 : (2 : ℝ) - 9 / 10 = 11 / 10 := by norm_num
  have h4 : (2 : ℝ) + 2 * (9 / 10) = 19 / 5 := by norm_num
  have h5 : (9 / 10 : ℝ) ^ 2 = 81 / 100 := by norm_num
  simp only [familyEnergyDeriv, h1, h2, h3, h4, h5]
  have x3hi : Real.sqrt 3 < 1.782 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have b1 : -4.4 < -2 * Real.sqrt 3 / (81 / 100) := by
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 81 / 100)]
    nlinarith
  have b2 : 16 < 3 * (9 / 10) / (2 * (Real.sqrt (19 / 100)) ^ 3) := by
    have hy : Real.sqrt (19 / 100) < 0.438 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    have hc : (Real.sqrt (19 / 100)) ^ 3 < (0.438 : ℝ) ^ 3 :=
      pow_lt_pow_left₀ hy (by positivity) (by norm_num)
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * (Real.sqrt (19 / 100)) ^ 3)]
    nlinarith
  have b3 : 0 < 6 * (9 / 10) / (Real.sqrt (319 / 100)) ^ 3 := by positivity
  have b4 : 5 < 6 / (Real.sqrt (11 / 10)) ^ 3 := by
    have hy : Real.sqrt (11 / 10) < 1.05 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    have hc : (Real.sqrt (11 / 10)) ^ 3 < (1.05 : ℝ) ^ 3 :=
      pow_lt_pow_left₀ hy (by positivity) (by norm_num)
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < (Real.sqrt (11 / 10)) ^ 3)]
    nlinarith
  have b5 : -1 < -(6 / (Real.sqrt (19 / 5)) ^ 3) := by
    rw [← neg_div]
    have hy : (1.82 : ℝ) < Real.sqrt (19 / 5) := by
      rw [Real.lt_sqrt (by norm_num)]
      norm_num
    have hc : (1.82 : ℝ) ^ 3 < (Real.sqrt (19 / 5)) ^ 3 :=
      pow_lt_pow_left₀ hy (by norm_num) (by norm_num)
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < (Real.sqrt (19 / 5)) ^ 3)]
    nlinarith
  linarith

lemma continuousOn_familyEnergyDeriv :
    ContinuousOn familyEnergyDeriv (Set.Icc (1 / 2 : ℝ) (9 / 10)) := by
  unfold familyEnergyDeriv
  have c1 : ContinuousOn (fun x : ℝ => Real.sqrt (1 - x ^ 2))
      (Set.Icc (1 / 2 : ℝ) (9 / 10)) := ContinuousOn.sqrt (by fun_prop)
  have c2 : ContinuousOn (fun x : ℝ => Real.sqrt (4 - x ^ 2))
      (Set.Icc (1 / 2 : ℝ) (9 / 10)) := ContinuousOn.sqrt (by fun_prop)
  have c3 : ContinuousOn (fun x : ℝ => Real.sqrt (2 - x))
      (Set.Icc (1 / 2 : ℝ) (9 / 10)) := ContinuousOn.sqrt (by fun_prop)
  have c4 : ContinuousOn (fun x : ℝ => Real.sqrt (2 + 2 * x))
      (Set.Icc (1 / 2 : ℝ) (9 / 10)) := ContinuousOn.sqrt (by fun_prop)
  have nz0 : ∀ x ∈ Set.Icc (1 / 2 : ℝ) (9 / 10), x ^ 2 ≠ 0 := by
    intro x hx
    have hx0 : x ≠ 0 := by
      intro h
      rw [h] at hx
      linarith [hx.1]
    exact pow_ne_zero 2 hx0
  have nz1 : ∀ x ∈ Set.Icc (1 / 2 : ℝ) (9 / 10), Real.sqrt (1 - x ^ 2) ≠ 0 := by
    intro x hx
    have h : (0 : ℝ) < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    exact ne_of_gt (Real.sqrt_pos.mpr h)
  have nz2 : ∀ x ∈ Set.Icc (1 / 2 : ℝ) (9 / 10),
      2 * (Real.sqrt (1 - x ^ 2)) ^ 3 ≠ 0 := by
    intro x hx
    exact mul_ne_zero (by norm_num) (pow_ne_zero 3 (nz1 x hx))
  have nz3 : ∀ x ∈ Set.Icc (1 / 2 : ℝ) (9 / 10), (Real.sqrt (4 - x ^ 2)) ^ 3 ≠ 0 := by
    intro x hx
    have h : (0 : ℝ) < 4 - x ^ 2 := by nlinarith [hx.1, hx.2]
    exact pow_ne_zero 3 (ne_of_gt (Real.sqrt_pos.mpr h))
  have nz4 : ∀ x ∈ Set.Icc (1 / 2 : ℝ) (9 / 10), (Real.sqrt (2 - x)) ^ 3 ≠ 0 := by
    intro x hx
    have h : (0 : ℝ) < 2 - x := by linarith [hx.2]
    exact pow_ne_zero 3 (ne_of_gt (Real.sqrt_pos.mpr h))
  have nz5 : ∀ x ∈ Set.Icc (1 / 2 : ℝ) (9 / 10), (Real.sqrt (2 + 2 * x)) ^ 3 ≠ 0 := by
    intro x hx
    have h : (0 : ℝ) < 2 + 2 * x := by linarith [hx.1]
    exact pow_ne_zero 3 (ne_of_gt (Real.sqrt_pos.mpr h))
  have ct1 : ContinuousOn (fun x : ℝ => -2 * Real.sqrt 3 / x ^ 2)
      (Set.Icc (1 / 2 : ℝ) (9 / 10)) :=
    (continuousOn_const (c := -2 * Real.sqrt 3)).div (by fun_prop) nz0
  have ct2 : ContinuousOn (fun x : ℝ => 3 * x / (2 * (Real.sqrt (1 - x ^ 2)) ^ 3))
      (Set.Icc (1 / 2 : ℝ) (9 / 10)) :=
    ContinuousOn.div (by fun_prop) ((c1.pow 3).const_mul 2) nz2
  have ct3 : ContinuousOn (fun x : ℝ => 6 * x / (Real.sqrt (4 - x ^ 2)) ^ 3)
      (Set.Icc (1 / 2 : ℝ) (9 / 10)) :=
    ContinuousOn.div (by fun_prop) (c2.pow 3) nz3
  have ct4 : ContinuousOn (fun x : ℝ => 6 / (Real.sqrt (2 - x)) ^ 3)
      (Set.Icc (1 / 2 : ℝ) (9 / 10)) :=
    (continuousOn_const (c := 6)).div (c3.pow 3) nz4
  have ct5 : ContinuousOn (fun x : ℝ => 6 / (Real.sqrt (2 + 2 * x)) ^ 3)
      (Set.Icc (1 / 2 : ℝ) (9 / 10)) :=
    (continuousOn_const (c := 6)).div (c4.pow 3) nz5
  exact ((((ct1.add ct2).add ct3).add ct4).sub ct5)

theorem exists_familyEnergyDeriv_zero :
    ∃ r ∈ Set.Icc (1 / 2 : ℝ) (9 / 10), familyEnergyDeriv r = 0 := by
  have hsub := intermediate_value_Icc (by norm_num : (1 / 2 : ℝ) ≤ 9 / 10)
    continuousOn_familyEnergyDeriv
  have hmem : (0 : ℝ) ∈ Set.Icc (familyEnergyDeriv (1 / 2)) (familyEnergyDeriv (9 / 10)) :=
    ⟨le_of_lt familyEnergyDeriv_half_neg, le_of_lt familyEnergyDeriv_nine_tenths_pos⟩
  rcases hsub hmem with ⟨r, hr, hzero⟩
  exact ⟨r, hr, hzero⟩

theorem exists_stationary_point :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ HasDerivAt familyEnergy (familyEnergyDeriv r) r ∧
      familyEnergyDeriv r = 0 := by
  rcases exists_familyEnergyDeriv_zero with ⟨r, hr, hzero⟩
  have h1 : 0 < r := by linarith [hr.1]
  have h2 : r < 1 := by linarith [hr.2]
  exact ⟨r, h1, h2, hasDerivAt_familyEnergy r h1 h2, hzero⟩

end ThomsonNine.Family
