import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring

/-! DRAFT_NOT_COMPILED: the attempted Lean invocation stopped at the missing Mathlib
import before checking these proofs. Recompile after the parent cache download completes.
Finite algebraic Hermite factorization. Independent of analytic remainder theorems,
interval code, numerical coefficients, and Thomson optimality. -/
namespace ThomsonNine.HermiteFactor
open Polynomial

variable {K : Type*} [Field K]

/-- A polynomial vanishing with its formal derivative has a double linear factor. -/
theorem square_linear_dvd_of_eval_derivative_zero (p : K[X]) (a : K)
    (hp : p.eval a = 0) (hd : p.derivative.eval a = 0) :
    (X - C a) ^ 2 ∣ p := by
  obtain ⟨q, hq⟩ := (dvd_iff_isRoot.mpr hp : X - C a ∣ p)
  have hq0 : q.eval a = 0 := by
    rw [hq] at hd
    simpa only [derivative_mul, derivative_X_sub_C, one_mul, eval_add,
      eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero] using hd
  obtain ⟨s, hs⟩ := (dvd_iff_isRoot.mpr hq0 : X - C a ∣ q)
  refine ⟨s, ?_⟩
  rw [hq, hs, pow_two, mul_assoc]

/-- The polynomial whose positivity will imply the Hermite minorant inequality. -/
noncomputable def G (H : K[X]) : K[X] := 1 - (C 2 - C 2 * X) * H ^ 2

/-- Only algebraic node data are needed; no analytic derivative of f is assumed. -/
theorem G_eval_zero (H : K[X]) (a : K)
    (hv : (2 - 2 * a) * (H.eval a) ^ 2 = 1) : (G H).eval a = 0 := by
  simp only [G, eval_sub, eval_one, eval_mul, eval_C, eval_X, eval_pow]
  rw [hv, sub_self]

theorem G_derivative_eval_zero (H : K[X]) (a : K)
    (hv : (2 - 2 * a) * (H.eval a) ^ 2 = 1)
    (hd : H.derivative.eval a = (H.eval a) ^ 3) :
    (G H).derivative.eval a = 0 := by
  have identity : (G H).derivative.eval a =
      2 * (H.eval a) ^ 2 * (1 - (2 - 2 * a) * (H.eval a) ^ 2) := by
    simp [G, pow_two, derivative_mul, derivative_sub, hd]
    ring
  rw [identity, hv, sub_self, mul_zero]

/-- Injectivity gives pairwise coprime squared node factors. -/
theorem pairwise_coprime_square_linear {I : Type*} (xi : I → K)
    (hi : Function.Injective xi) :
    Pairwise (fun i j => IsCoprime ((X - C (xi i)) ^ 2 : K[X])
      ((X - C (xi j)) ^ 2)) := by
  intro i j hij
  exact (Polynomial.pairwise_coprime_X_sub_C hi hij).pow

/-- Generic finite-node double-factor divisibility. -/
theorem product_square_linear_dvd {I : Type*} [Fintype I]
    (p : K[X]) (xi : I → K) (hi : Function.Injective xi)
    (hp : ∀ i, p.eval (xi i) = 0)
    (hd : ∀ i, p.derivative.eval (xi i) = 0) :
    (∏ i, (X - C (xi i)) ^ 2) ∣ p := by
  apply Fintype.prod_dvd_of_coprime (pairwise_coprime_square_linear xi hi)
  intro i
  exact square_linear_dvd_of_eval_derivative_zero p (xi i) (hp i) (hd i)

/-- Hermite node identities force exact G = W Q, without remainder enclosures. -/
theorem exists_hermite_quotient {I : Type*} [Fintype I]
    (H : K[X]) (xi : I → K) (hi : Function.Injective xi)
    (hv : ∀ i, (2 - 2 * xi i) * (H.eval (xi i)) ^ 2 = 1)
    (hd : ∀ i, H.derivative.eval (xi i) = (H.eval (xi i)) ^ 3) :
    ∃ Q : K[X], G H = (∏ i, (X - C (xi i)) ^ 2) * Q := by
  exact product_square_linear_dvd (G H) xi hi
    (fun i => G_eval_zero H (xi i) (hv i))
    (fun i => G_derivative_eval_zero H (xi i) (hv i) (hd i))

end ThomsonNine.HermiteFactor
