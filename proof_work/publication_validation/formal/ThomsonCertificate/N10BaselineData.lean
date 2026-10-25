import ThomsonCertificate.DelsarteBridge

/-! Exact rational data for the current n=10 Delsarte/Legendre baseline.

This module records only the coefficient and counting arithmetic.  It does not
instantiate the spherical addition theorem or the polynomial minorant; those
remain explicit obligations of `DelsarteBridge`. -/

namespace ThomsonTen

open ThomsonCertificate

noncomputable def n10BaselineCoeff : Fin 13 → ℝ := ![
  (41269 / 50000 : ℝ), (25267 / 50000 : ℝ), (3233 / 12500 : ℝ),
  (10131 / 100000 : ℝ), (47 / 2000 : ℝ), 0, 0, (109 / 50000 : ℝ),
  (131 / 100000 : ℝ), 0, 0, 0, 0]

theorem n10BaselineCoeff_nonneg (k : Fin 13) : 0 ≤ n10BaselineCoeff k := by
  fin_cases k <;> norm_num [n10BaselineCoeff]

theorem n10Baseline_a0 : n10BaselineCoeff 0 = (41269 / 50000 : ℝ) := by
  rfl

theorem n10BaselineCoeff_sum :
    ∑ k : Fin 13, n10BaselineCoeff k = (85883 / 50000 : ℝ) := by
  norm_num [n10BaselineCoeff, Fin.sum_univ_succ]

theorem n10Baseline_pair_count : ((10 : ℝ) * 10 - 10) / 2 = 45 := by
  norm_num

theorem n10Baseline_lower_bound_arithmetic :
    ((10 : ℝ)^2 / 2) * n10BaselineCoeff 0 -
      (10 / 2) * ∑ k : Fin 13, n10BaselineCoeff k =
        (326807 / 10000 : ℝ) := by
  rw [n10Baseline_a0, n10BaselineCoeff_sum]
  norm_num

/- The coefficient/counting part can be consumed independently of the
   analytic obligations in `DelsarteBridge`. -/
theorem n10Baseline_bookkeeping_identity :
    ((10 : ℝ)^2 / 2) * n10BaselineCoeff 0 -
        (10 / 2) * ∑ k : Fin 13, n10BaselineCoeff k =
      (326807 / 10000 : ℝ) ∧
    ((10 : ℝ) * 10 - 10) / 2 = 45 := by
  constructor
  · exact n10Baseline_lower_bound_arithmetic
  · exact n10Baseline_pair_count

end ThomsonTen
