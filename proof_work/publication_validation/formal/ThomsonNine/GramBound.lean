/-
Gram-matrix constraints of the physical domain.

For three unit vectors `a b c`, the Gram determinant of `a,b,c` is
nonnegative.  With `u = ⟪a,b⟫`, `v = ⟪a,c⟫`, `t = ⟪b,c⟫` and
`‖a‖ = ‖b‖ = ‖c‖ = 1` that determinant is exactly

`gram u v t = 1 + 2*u*v*t - u^2 - v^2 - t^2`.

We prove `0 ≤ gram u v t` by Cauchy-Schwarz: subtracting the projections of
`b` and `c` onto `a` gives `(t - u*v)^2 ≤ (1 - u^2)*(1 - v^2)`, which is the
Gram determinant.  Hence the Gram constraint of the domain `D` is a necessary
consequence of the unit-norm constraints, not an extra assumption.  We also
record `-1 ≤ ⟪a,b⟫ ≤ 1`.

This file proves geometric facts only; it contains no `sorry` or `axiom`.
-/
import ThomsonNine.LeafSemantics
import ThomsonNine.Statement
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open scoped BigOperators InnerProductSpace

namespace ThomsonNine

open ThomsonNine.Semantics (gram)

/-- The Gram determinant of three unit vectors equals the domain Gram
polynomial in their three pairwise inner products, and is nonnegative. -/
theorem gram_inner_nonneg (a b c : R3) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    0 ≤ gram (⟪a, b⟫_ℝ) (⟪a, c⟫_ℝ) (⟪b, c⟫_ℝ) := by
  have haa : ⟪a, a⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, ha]; norm_num
  have hbb : ⟪b, b⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hb]; norm_num
  have hcc : ⟪c, c⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hc]; norm_num
  have hb' : ⟪b - (⟪a, b⟫_ℝ) • a, b - (⟪a, b⟫_ℝ) • a⟫_ℝ = 1 - (⟪a, b⟫_ℝ) ^ 2 := by
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm b a, hbb, haa]
    ring
  have hc' : ⟪c - (⟪a, c⟫_ℝ) • a, c - (⟪a, c⟫_ℝ) • a⟫_ℝ = 1 - (⟪a, c⟫_ℝ) ^ 2 := by
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm c a, hcc, haa]
    ring
  have hbc : ⟪b - (⟪a, b⟫_ℝ) • a, c - (⟪a, c⟫_ℝ) • a⟫_ℝ =
      ⟪b, c⟫_ℝ - ⟪a, b⟫_ℝ * ⟪a, c⟫_ℝ := by
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm b a, haa]
    ring
  have hcs := real_inner_mul_inner_self_le (b - (⟪a, b⟫_ℝ) • a) (c - (⟪a, c⟫_ℝ) • a)
  rw [hb', hc', hbc] at hcs
  unfold gram
  nlinarith [hcs]

/-- Every inner product of two unit vectors lies in `[-1,1]`. -/
theorem inner_mem_Icc_of_unit (a b : R3) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ⟪a, b⟫_ℝ ∈ Set.Icc (-1 : ℝ) 1 := by
  have h := abs_real_inner_le_norm a b
  rw [ha, hb, mul_one] at h
  exact abs_le.mp h

/-- For a nine-point sphere configuration, every pairwise inner product lies
in `[-1,1]`. -/
theorem inner_mem_Icc_of_mem (x : Fin 9 → R3) (hx : x ∈ SphereConfig 9) (i j : Fin 9) :
    ⟪x i, x j⟫_ℝ ∈ Set.Icc (-1 : ℝ) 1 :=
  inner_mem_Icc_of_unit (x i) (x j) (hx.1 i) (hx.1 j)

/-- For a nine-point sphere configuration, every triple satisfies the Gram
constraint `0 ≤ gram u v t` of the domain `D`. -/
theorem gram_constraint_of_mem (x : Fin 9 → R3) (hx : x ∈ SphereConfig 9) (i j k : Fin 9) :
    0 ≤ gram (⟪x i, x j⟫_ℝ) (⟪x i, x k⟫_ℝ) (⟪x j, x k⟫_ℝ) :=
  gram_inner_nonneg (x i) (x j) (x k) (hx.1 i) (hx.1 j) (hx.1 k)

end ThomsonNine
