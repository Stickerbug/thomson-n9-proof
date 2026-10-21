import ThomsonNine.Stationary
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open ThomsonNine.Family
namespace ThomsonNine.Family

/-! The second derivative of the one-parameter family energy, its positivity on
`(0, 1)`, and uniqueness of the stationary point. -/

noncomputable def familyEnergyDeriv2 (r : ℝ) : ℝ :=
  4 * Real.sqrt 3 / r ^ 3
  + (3 / 2) * ((Real.sqrt (1 - r ^ 2))⁻¹) ^ 3
  + (9 / 2) * r ^ 2 * ((Real.sqrt (1 - r ^ 2))⁻¹) ^ 5
  + 6 * ((Real.sqrt (4 - r ^ 2))⁻¹) ^ 3
  + 18 * r ^ 2 * ((Real.sqrt (4 - r ^ 2))⁻¹) ^ 5
  + 9 * ((Real.sqrt (2 - r))⁻¹) ^ 5
  + 18 * ((Real.sqrt (2 + 2 * r))⁻¹) ^ 5

lemma hasDerivAt_inv_sqrt_quadratic_cube (a x : ℝ) (hx : 0 < a - x ^ 2) :
    HasDerivAt (fun y : ℝ => ((Real.sqrt (a - y ^ 2))⁻¹) ^ 3)
      (3 * x * ((Real.sqrt (a - x ^ 2))⁻¹) ^ 5) x := by
  have h := (hasDerivAt_inv_sqrt_quadratic a x hx).pow 3
  convert h using 1
  ring_nf

lemma hasDerivAt_inv_sqrt_linear_cube (a x : ℝ) (hx : 0 < a - x) :
    HasDerivAt (fun y : ℝ => ((Real.sqrt (a - y))⁻¹) ^ 3)
      ((3 / 2) * ((Real.sqrt (a - x))⁻¹) ^ 5) x := by
  have h := (hasDerivAt_inv_sqrt_linear a x hx).pow 3
  convert h using 1
  ring_nf

lemma hasDerivAt_inv_sqrt_affine_cube (b x : ℝ) (hx : 0 < b + 2 * x) :
    HasDerivAt (fun y : ℝ => ((Real.sqrt (b + 2 * y))⁻¹) ^ 3)
      (-3 * ((Real.sqrt (b + 2 * x))⁻¹) ^ 5) x := by
  have h := (hasDerivAt_inv_sqrt_affine b x hx).pow 3
  convert h using 1
  ring_nf

lemma hasDerivAt_neg_sqrt3_div_sq (r : ℝ) (hr : 0 < r) :
    HasDerivAt (fun y : ℝ => -2 * Real.sqrt 3 * (y ^ 2)⁻¹)
      (4 * Real.sqrt 3 / r ^ 3) r := by
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * r) r := by
    simpa using hasDerivAt_pow 2 r
  have hinv : HasDerivAt (fun y : ℝ => 1 / y ^ 2)
      ((0 * (r ^ 2) - 1 * (2 * r)) / (r ^ 2) ^ 2) r :=
    (hasDerivAt_const (x := r) (c := 1)).div hsq (by positivity : r ^ 2 ≠ 0)
  have h := hinv.const_mul (-2 * Real.sqrt 3)
  convert h using 1
  · funext y
    rw [one_div]
  · field_simp [hr.ne']
    ring

theorem hasDerivAt_familyEnergyDeriv (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt familyEnergyDeriv (familyEnergyDeriv2 r) r := by
  unfold familyEnergyDeriv
  have h1 : HasDerivAt (fun y : ℝ => -2 * Real.sqrt 3 * (y ^ 2)⁻¹)
      (4 * Real.sqrt 3 / r ^ 3) r := hasDerivAt_neg_sqrt3_div_sq r hr
  have hu1 : HasDerivAt (fun y : ℝ => ((Real.sqrt (1 - y ^ 2))⁻¹) ^ 3)
      (3 * r * ((Real.sqrt (1 - r ^ 2))⁻¹) ^ 5) r :=
    hasDerivAt_inv_sqrt_quadratic_cube 1 r (by nlinarith)
  have h2 : HasDerivAt
      (fun y : ℝ => (3 / 2) * (y * ((Real.sqrt (1 - y ^ 2))⁻¹) ^ 3))
      ((3 / 2) * (((Real.sqrt (1 - r ^ 2))⁻¹) ^ 3 +
        r * (3 * r * ((Real.sqrt (1 - r ^ 2))⁻¹) ^ 5))) r := by
    have hm := ((hasDerivAt_id r).mul hu1).const_mul (3 / 2)
    convert hm using 1
    · funext y
      simp
    · simp only [id_eq]
      ring
  have hu2 : HasDerivAt (fun y : ℝ => ((Real.sqrt (4 - y ^ 2))⁻¹) ^ 3)
      (3 * r * ((Real.sqrt (4 - r ^ 2))⁻¹) ^ 5) r :=
    hasDerivAt_inv_sqrt_quadratic_cube 4 r (by nlinarith)
  have h3 : HasDerivAt
      (fun y : ℝ => 6 * (y * ((Real.sqrt (4 - y ^ 2))⁻¹) ^ 3))
      (6 * (((Real.sqrt (4 - r ^ 2))⁻¹) ^ 3 +
        r * (3 * r * ((Real.sqrt (4 - r ^ 2))⁻¹) ^ 5))) r := by
    have hm := ((hasDerivAt_id r).mul hu2).const_mul 6
    convert hm using 1
    · funext y
      simp
    · simp only [id_eq]
      ring
  have hu3 : HasDerivAt (fun y : ℝ => ((Real.sqrt (2 - y))⁻¹) ^ 3)
      ((3 / 2) * ((Real.sqrt (2 - r))⁻¹) ^ 5) r :=
    hasDerivAt_inv_sqrt_linear_cube 2 r (by linarith)
  have h4 : HasDerivAt (fun y : ℝ => 6 * ((Real.sqrt (2 - y))⁻¹) ^ 3)
      (6 * ((3 / 2) * ((Real.sqrt (2 - r))⁻¹) ^ 5)) r :=
    hu3.const_mul 6
  have hu4 : HasDerivAt (fun y : ℝ => ((Real.sqrt (2 + 2 * y))⁻¹) ^ 3)
      (-3 * ((Real.sqrt (2 + 2 * r))⁻¹) ^ 5) r :=
    hasDerivAt_inv_sqrt_affine_cube 2 r (by linarith)
  have h5 : HasDerivAt (fun y : ℝ => -6 * ((Real.sqrt (2 + 2 * y))⁻¹) ^ 3)
      (-6 * (-3 * ((Real.sqrt (2 + 2 * r))⁻¹) ^ 5)) r :=
    hu4.const_mul (-6)
  have hsum := ((((h1.add h2).add h3).add h4).add h5)
  convert hsum using 1
  · funext y
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq]
    ring_nf
  · simp only [familyEnergyDeriv2]
    ring_nf

lemma familyEnergyDeriv2_pos (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    0 < familyEnergyDeriv2 r := by
  have h1 : (0 : ℝ) < 1 - r ^ 2 := by nlinarith
  have h2 : (0 : ℝ) < 4 - r ^ 2 := by nlinarith
  have h3 : (0 : ℝ) < 2 - r := by linarith
  have h4 : (0 : ℝ) < 2 + 2 * r := by linarith
  have s1 : (0 : ℝ) < Real.sqrt (1 - r ^ 2) := Real.sqrt_pos.mpr h1
  have s2 : (0 : ℝ) < Real.sqrt (4 - r ^ 2) := Real.sqrt_pos.mpr h2
  have s3 : (0 : ℝ) < Real.sqrt (2 - r) := Real.sqrt_pos.mpr h3
  have s4 : (0 : ℝ) < Real.sqrt (2 + 2 * r) := Real.sqrt_pos.mpr h4
  unfold familyEnergyDeriv2
  positivity

lemma continuousOn_familyEnergyDeriv_Ioo :
    ContinuousOn familyEnergyDeriv (Set.Ioo (0 : ℝ) 1) := by
  unfold familyEnergyDeriv
  have c1 : ContinuousOn (fun x : ℝ => Real.sqrt (1 - x ^ 2)) (Set.Ioo (0 : ℝ) 1) :=
    ContinuousOn.sqrt (by fun_prop)
  have c2 : ContinuousOn (fun x : ℝ => Real.sqrt (4 - x ^ 2)) (Set.Ioo (0 : ℝ) 1) :=
    ContinuousOn.sqrt (by fun_prop)
  have c3 : ContinuousOn (fun x : ℝ => Real.sqrt (2 - x)) (Set.Ioo (0 : ℝ) 1) :=
    ContinuousOn.sqrt (by fun_prop)
  have c4 : ContinuousOn (fun x : ℝ => Real.sqrt (2 + 2 * x)) (Set.Ioo (0 : ℝ) 1) :=
    ContinuousOn.sqrt (by fun_prop)
  have nz0 : ∀ x ∈ Set.Ioo (0 : ℝ) 1, x ^ 2 ≠ 0 := by
    intro x hx
    exact pow_ne_zero 2 (ne_of_gt hx.1)
  have nz1 : ∀ x ∈ Set.Ioo (0 : ℝ) 1, Real.sqrt (1 - x ^ 2) ≠ 0 := by
    intro x hx
    have h : (0 : ℝ) < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    exact ne_of_gt (Real.sqrt_pos.mpr h)
  have nz2 : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 2 * (Real.sqrt (1 - x ^ 2)) ^ 3 ≠ 0 := by
    intro x hx
    exact mul_ne_zero (by norm_num) (pow_ne_zero 3 (nz1 x hx))
  have nz3 : ∀ x ∈ Set.Ioo (0 : ℝ) 1, (Real.sqrt (4 - x ^ 2)) ^ 3 ≠ 0 := by
    intro x hx
    have h : (0 : ℝ) < 4 - x ^ 2 := by nlinarith [hx.1, hx.2]
    exact pow_ne_zero 3 (ne_of_gt (Real.sqrt_pos.mpr h))
  have nz4 : ∀ x ∈ Set.Ioo (0 : ℝ) 1, (Real.sqrt (2 - x)) ^ 3 ≠ 0 := by
    intro x hx
    have h : (0 : ℝ) < 2 - x := by linarith [hx.2]
    exact pow_ne_zero 3 (ne_of_gt (Real.sqrt_pos.mpr h))
  have nz5 : ∀ x ∈ Set.Ioo (0 : ℝ) 1, (Real.sqrt (2 + 2 * x)) ^ 3 ≠ 0 := by
    intro x hx
    have h : (0 : ℝ) < 2 + 2 * x := by linarith [hx.1]
    exact pow_ne_zero 3 (ne_of_gt (Real.sqrt_pos.mpr h))
  have ct1 : ContinuousOn (fun x : ℝ => -2 * Real.sqrt 3 / x ^ 2) (Set.Ioo (0 : ℝ) 1) :=
    (continuousOn_const (c := -2 * Real.sqrt 3)).div (by fun_prop) nz0
  have ct2 : ContinuousOn (fun x : ℝ => 3 * x / (2 * (Real.sqrt (1 - x ^ 2)) ^ 3))
      (Set.Ioo (0 : ℝ) 1) :=
    ContinuousOn.div (by fun_prop) ((c1.pow 3).const_mul 2) nz2
  have ct3 : ContinuousOn (fun x : ℝ => 6 * x / (Real.sqrt (4 - x ^ 2)) ^ 3)
      (Set.Ioo (0 : ℝ) 1) :=
    ContinuousOn.div (by fun_prop) (c2.pow 3) nz3
  have ct4 : ContinuousOn (fun x : ℝ => 6 / (Real.sqrt (2 - x)) ^ 3) (Set.Ioo (0 : ℝ) 1) :=
    (continuousOn_const (c := 6)).div (c3.pow 3) nz4
  have ct5 : ContinuousOn (fun x : ℝ => 6 / (Real.sqrt (2 + 2 * x)) ^ 3) (Set.Ioo (0 : ℝ) 1) :=
    (continuousOn_const (c := 6)).div (c4.pow 3) nz5
  exact ((((ct1.add ct2).add ct3).add ct4).sub ct5)

theorem stationary_point_unique :
    ∀ r s : ℝ, 0 < r → r < 1 → 0 < s → s < 1 →
      familyEnergyDeriv r = 0 → familyEnergyDeriv s = 0 → r = s := by
  intro r s hr hr1 hs hs1 hzr hzs
  rcases lt_trichotomy r s with h | h | h
  · exfalso
    have hcont : ContinuousOn familyEnergyDeriv (Set.Icc r s) :=
      continuousOn_familyEnergyDeriv_Ioo.mono (by
        intro x hx
        exact Set.mem_Ioo.mpr ⟨lt_of_lt_of_le hr hx.1, lt_of_le_of_lt hx.2 hs1⟩)
    have hrolle := exists_hasDerivAt_eq_zero (f := familyEnergyDeriv)
      (f' := familyEnergyDeriv2) h hcont (by rw [hzr, hzs])
      (fun x hx => hasDerivAt_familyEnergyDeriv x (lt_trans hr hx.1)
        (lt_trans hx.2 hs1))
    rcases hrolle with ⟨c, hc, hczero⟩
    have hc1 : 0 < c := lt_trans hr hc.1
    have hc2 : c < 1 := lt_trans hc.2 hs1
    exact absurd hczero (ne_of_gt (familyEnergyDeriv2_pos c hc1 hc2))
  · exact h
  · exfalso
    have hcont : ContinuousOn familyEnergyDeriv (Set.Icc s r) :=
      continuousOn_familyEnergyDeriv_Ioo.mono (by
        intro x hx
        exact Set.mem_Ioo.mpr ⟨lt_of_lt_of_le hs hx.1, lt_of_le_of_lt hx.2 hr1⟩)
    have hrolle := exists_hasDerivAt_eq_zero (f := familyEnergyDeriv)
      (f' := familyEnergyDeriv2) h hcont (by rw [hzs, hzr])
      (fun x hx => hasDerivAt_familyEnergyDeriv x (lt_trans hs hx.1)
        (lt_trans hx.2 hr1))
    rcases hrolle with ⟨c, hc, hczero⟩
    have hc1 : 0 < c := lt_trans hs hc.1
    have hc2 : c < 1 := lt_trans hc.2 hr1
    exact absurd hczero (ne_of_gt (familyEnergyDeriv2_pos c hc1 hc2))

theorem stationary_point_unique' (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hzero : familyEnergyDeriv r = 0) :
    ∀ s : ℝ, 0 < s → s < 1 → HasDerivAt familyEnergy 0 s → s = r := by
  intro s hs hs1 hder
  have hd : HasDerivAt familyEnergy (familyEnergyDeriv s) s := hasDerivAt_familyEnergy s hs hs1
  have hzs : familyEnergyDeriv s = 0 := (hder.unique hd).symm
  exact stationary_point_unique s r hs hs1 hr hr1 hzs hzero

theorem exists_unique_stationary_point :
    ∃! r : ℝ, 0 < r ∧ r < 1 ∧ HasDerivAt familyEnergy (familyEnergyDeriv r) r ∧
      familyEnergyDeriv r = 0 := by
  rcases exists_stationary_point with ⟨r, hr, hr1, hderiv, hzero⟩
  refine ⟨r, ⟨hr, hr1, hderiv, hzero⟩, ?_⟩
  rintro s ⟨hs, hs1, hders, hzs⟩
  exact (stationary_point_unique r s hr hr1 hs hs1 hzero hzs).symm

end ThomsonNine.Family
