import ThomsonNine.Family
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add

open Real
open ThomsonNine

namespace ThomsonNine.Family

/-! Derivatives of the six terms of `familyEnergy`. -/

noncomputable def familyEnergyDeriv (r : ℝ) : ℝ :=
  -2 * Real.sqrt 3 / r ^ 2
  + 3 * r / (2 * (Real.sqrt (1 - r ^ 2)) ^ 3)
  + 6 * r / (Real.sqrt (4 - r ^ 2)) ^ 3
  + 6 / (Real.sqrt (2 - r)) ^ 3
  - 6 / (Real.sqrt (2 + 2 * r)) ^ 3

lemma hasDerivAt_inv_sqrt_quadratic (a x : ℝ) (hx : 0 < a - x ^ 2) :
    HasDerivAt (fun y : ℝ => (Real.sqrt (a - y ^ 2))⁻¹)
      (x / (Real.sqrt (a - x ^ 2)) ^ 3) x := by
  have hsqrt_ne : Real.sqrt (a - x ^ 2) ≠ 0 := by positivity
  have hinner : HasDerivAt (fun y : ℝ => a - y ^ 2) (-(2 * x)) x := by
    have h := (hasDerivAt_const (x := x) (c := a)).sub (hasDerivAt_pow 2 x)
    convert h using 1
    ring
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (a - x ^ 2))) (a - x ^ 2) :=
    Real.hasDerivAt_sqrt (ne_of_gt hx)
  have hcomp : HasDerivAt (fun y : ℝ => Real.sqrt (a - y ^ 2))
      ((1 / (2 * Real.sqrt (a - x ^ 2))) * (-(2 * x))) x :=
    hsqrt.comp x hinner
  have hinv := hcomp.inv hsqrt_ne
  convert hinv using 1
  all_goals (try field_simp; try ring)

lemma hasDerivAt_inv_sqrt_linear (a x : ℝ) (hx : 0 < a - x) :
    HasDerivAt (fun y : ℝ => (Real.sqrt (a - y))⁻¹)
      (1 / (2 * (Real.sqrt (a - x)) ^ 3)) x := by
  have hsqrt_ne : Real.sqrt (a - x) ≠ 0 := by positivity
  have hinner : HasDerivAt (fun y : ℝ => a - y) (-1) x := by
    have h := (hasDerivAt_const (x := x) (c := a)).sub (hasDerivAt_id x)
    convert h using 1
    · funext y
      simp
    · ring
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (a - x))) (a - x) :=
    Real.hasDerivAt_sqrt (ne_of_gt hx)
  have hcomp : HasDerivAt (fun y : ℝ => Real.sqrt (a - y))
      ((1 / (2 * Real.sqrt (a - x))) * (-1)) x :=
    hsqrt.comp x hinner
  have hinv := hcomp.inv hsqrt_ne
  convert hinv using 1
  all_goals (try field_simp; try ring)

lemma hasDerivAt_inv_sqrt_affine (b x : ℝ) (hx : 0 < b + 2 * x) :
    HasDerivAt (fun y : ℝ => (Real.sqrt (b + 2 * y))⁻¹)
      (-(1 / (Real.sqrt (b + 2 * x)) ^ 3)) x := by
  have hsqrt_ne : Real.sqrt (b + 2 * x) ≠ 0 := by positivity
  have hinner : HasDerivAt (fun y : ℝ => b + 2 * y) 2 x := by
    have h : HasDerivAt (fun y : ℝ => b + 2 * y) (0 + 2 * 1) x :=
      (hasDerivAt_const (x := x) (c := b)).add ((hasDerivAt_id x).const_mul 2)
    simpa using h
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (b + 2 * x))) (b + 2 * x) :=
    Real.hasDerivAt_sqrt (ne_of_gt hx)
  have hcomp : HasDerivAt (fun y : ℝ => Real.sqrt (b + 2 * y))
      ((1 / (2 * Real.sqrt (b + 2 * x))) * 2) x :=
    hsqrt.comp x hinner
  have hinv := hcomp.inv hsqrt_ne
  convert hinv using 1
  all_goals (try field_simp; try ring)

theorem hasDerivAt_familyEnergy (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt familyEnergy (familyEnergyDeriv r) r := by
  unfold familyEnergy
  have h1 : HasDerivAt (fun _ : ℝ => Real.sqrt 3) 0 r := hasDerivAt_const r _
  have h2 : HasDerivAt (fun y : ℝ => 2 * Real.sqrt 3 / y)
      (2 * Real.sqrt 3 * (-(r ^ 2)⁻¹)) r := by
    simpa only [div_eq_mul_inv] using (hasDerivAt_inv (ne_of_gt hr)).const_mul (2 * Real.sqrt 3)
  have h3 : HasDerivAt (fun y : ℝ => 3 / (2 * Real.sqrt (1 - y ^ 2)))
      ((3 / 2) * (r / (Real.sqrt (1 - r ^ 2)) ^ 3)) r := by
    have hbase := hasDerivAt_inv_sqrt_quadratic 1 r (by nlinarith)
    have h := hbase.const_mul (3 / 2 : ℝ)
    convert h using 1
    funext y
    rw [div_eq_mul_inv, mul_inv]
    ring
  have h4 : HasDerivAt (fun y : ℝ => 6 / Real.sqrt (4 - y ^ 2))
      (6 * (r / (Real.sqrt (4 - r ^ 2)) ^ 3)) r := by
    have hbase := hasDerivAt_inv_sqrt_quadratic 4 r (by nlinarith)
    simpa only [div_eq_mul_inv] using hbase.const_mul 6
  have h5 : HasDerivAt (fun y : ℝ => 12 / Real.sqrt (2 - y))
      (12 * (1 / (2 * (Real.sqrt (2 - r)) ^ 3))) r := by
    have hbase := hasDerivAt_inv_sqrt_linear 2 r (by linarith)
    simpa only [div_eq_mul_inv] using hbase.const_mul 12
  have h6 : HasDerivAt (fun y : ℝ => 6 / Real.sqrt (2 + 2 * y))
      (6 * (-(1 / (Real.sqrt (2 + 2 * r)) ^ 3))) r := by
    have hbase := hasDerivAt_inv_sqrt_affine 2 r (by linarith)
    simpa only [div_eq_mul_inv] using hbase.const_mul 6
  have hsum := ((((h1.add h2).add h3).add h4).add h5).add h6
  convert hsum using 1
  simp only [familyEnergyDeriv]
  field_simp
  ring

end ThomsonNine.Family
