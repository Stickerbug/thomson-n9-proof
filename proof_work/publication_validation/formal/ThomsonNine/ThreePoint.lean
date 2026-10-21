/-
The Bachoc–Vallentin three-point positivity theorem on the sphere S²,
adapted (with attribution) from the N=7 Lean formalization
`huwngtran/thomson-n7-lean`, commit 25f2fa5 (`ThreePoint` section).

The upstream project is a standalone `import Mathlib` monolith and is not
imported here; the relevant definitions and proofs are copied/adapted.
-/
import ThomsonNine.Statement
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination

open scoped BigOperators InnerProductSpace

namespace ThomsonNine

namespace ThreePoint

open Finset Matrix
open scoped RealInnerProductSpace

/-! # Bachoc–Vallentin three-point positivity on `S²` (any block size, any `k`)

`Q3 k u v t = ((1-u²)(1-v²))^{k/2} T_k((t-uv)/√((1-u²)(1-v²)))` via the Chebyshev recursion.
-/

/-- `Q_k(u,v,t)`: `Q_0 = 1`, `Q_1 = t - uv`,
`Q_{k+2} = 2 (t-uv) Q_{k+1} - (1-u²)(1-v²) Q_k`. -/
noncomputable def Q3 : ℕ → ℝ → ℝ → ℝ → ℝ
  | 0, _, _, _ => 1
  | 1, u, v, t => t - u * v
  | k + 2, u, v, t =>
      2 * (t - u * v) * Q3 (k + 1) u v t - (1 - u ^ 2) * (1 - v ^ 2) * Q3 k u v t

/-- `Y_k(u,v,t)_{ab} = uᵃ vᵇ Q_k(u,v,t)`, `a, b < m`. -/
noncomputable def Y3 (m k : ℕ) (u v t : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun a b => u ^ (a : ℕ) * v ^ (b : ℕ) * Q3 k u v t

/-- The Bachoc–Vallentin matrix `S_k = (1/6) Σ_{σ ∈ S₃} Y_k ∘ σ`, symmetric in `(u,v,t)`. -/
noncomputable def S3 (m k : ℕ) (u v t : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  (1 / 6 : ℝ) •
    (Y3 m k u v t + Y3 m k u t v + Y3 m k v u t + Y3 m k v t u + Y3 m k t u v + Y3 m k t v u)

/-- The Frobenius pairing `⟨A, B⟩ = Σ_{ab} A_{ab} B_{ab}`. -/
def matDot {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ) : ℝ := ∑ a, ∑ b, A a b * B a b

theorem S3_swap12 (m k : ℕ) (u v t : ℝ) : S3 m k u v t = S3 m k v u t := by
  ext i j
  simp only [S3, Y3, Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply, smul_eq_mul]
  ring

theorem S3_swap23 (m k : ℕ) (u v t : ℝ) : S3 m k u v t = S3 m k u t v := by
  ext i j
  simp only [S3, Y3, Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply, smul_eq_mul]
  ring

/-! ### Addition theorem (de Moivre) -/

theorem Q3_eq_re (u v t : ℝ) (z z' : ℂ)
    (hu : 1 - u ^ 2 = Complex.normSq z) (hv : 1 - v ^ 2 = Complex.normSq z')
    (ht : t - u * v = (z * (starRingEnd ℂ) z').re) (k : ℕ) :
    Q3 k u v t = ((z * (starRingEnd ℂ) z') ^ k).re := by
  set w : ℂ := z * (starRingEnd ℂ) z' with hw
  have hnw : Complex.normSq w = (1 - u ^ 2) * (1 - v ^ 2) := by
    rw [hw, map_mul, Complex.normSq_conj, hu, hv]
  have hrec : w * w = (2 * w.re : ℝ) * w - (Complex.normSq w : ℝ) := by
    apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring
  have key : ∀ k, Q3 k u v t = (w ^ k).re ∧ Q3 (k + 1) u v t = (w ^ (k + 1)).re := by
    intro k
    induction k with
    | zero => simp [Q3, ht]
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have h2 : w ^ (k + 2) = ((2 * w.re : ℝ) : ℂ) * w ^ (k + 1) - (Complex.normSq w : ℝ) * w ^ k := by
        have : w ^ (k + 2) = w ^ k * (w * w) := by ring
        rw [this, hrec]; ring
      show Q3 (k + 2) u v t = (w ^ (k + 2)).re
      rw [h2, Complex.sub_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, hnw, ← ih.1, ← ih.2, ← ht]
      simp only [Q3]
  exact (key k).1

/-- The quadratic form of `Σ_{j,l} Y_k` at a fixed centre is a sum of two squares. -/
theorem quad_Y3_nonneg (m k : ℕ) {n : ℕ} (u : Fin n → ℝ) (t : Fin n → Fin n → ℝ)
    (a b : Fin n → ℝ) (hu : ∀ j, 1 - u j ^ 2 = a j ^ 2 + b j ^ 2)
    (ht : ∀ j l, t j l - u j * u l = a j * a l + b j * b l)
    (w : Fin m → ℝ) :
    0 ≤ ∑ j, ∑ l, w ⬝ᵥ (Y3 m k (u j) (u l) (t j l)).mulVec w := by
  set z : Fin n → ℂ := fun j => ⟨a j, b j⟩ with hz
  have hQ : ∀ j l, Q3 k (u j) (u l) (t j l)
      = ((z j) ^ k).re * ((z l) ^ k).re + ((z j) ^ k).im * ((z l) ^ k).im := by
    intro j l
    rw [Q3_eq_re (u j) (u l) (t j l) (z j) (z l)
      (by rw [hu j]; simp [hz, Complex.normSq_apply, sq])
      (by rw [hu l]; simp [hz, Complex.normSq_apply, sq])
      (by simp [hz, ht])]
    rw [mul_pow, Complex.mul_re, ← map_pow, Complex.conj_re, Complex.conj_im]
    ring
  have key : ∀ j l, w ⬝ᵥ (Y3 m k (u j) (u l) (t j l)).mulVec w
      = (∑ p, w p * u j ^ (p : ℕ)) * (∑ p, w p * u l ^ (p : ℕ))
        * (((z j) ^ k).re * ((z l) ^ k).re + ((z j) ^ k).im * ((z l) ^ k).im) := by
    intro j l
    rw [← hQ j l]
    simp only [dotProduct, mulVec, Y3, Matrix.of_apply]
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  simp only [key]
  have hsq : ∀ (g c s : Fin n → ℝ), ∑ j, ∑ l, g j * g l * (c j * c l + s j * s l)
      = (∑ j, g j * c j) ^ 2 + (∑ j, g j * s j) ^ 2 := by
    intro g c s
    simp only [sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hsq (fun j => ∑ p, w p * u j ^ (p : ℕ)) (fun j => ((z j) ^ k).re) (fun j => ((z j) ^ k).im)]
  positivity

/-- Relabelling lemmas for triple sums. -/
theorem tsum_swap12 {ι : Type*} [Fintype ι] (g : ι → ι → ι → ℝ) :
    ∑ i, ∑ j, ∑ l, g i j l = ∑ i, ∑ j, ∑ l, g j i l := by
  rw [Finset.sum_comm]

theorem tsum_swap23 {ι : Type*} [Fintype ι] (g : ι → ι → ι → ℝ) :
    ∑ i, ∑ j, ∑ l, g i j l = ∑ i, ∑ j, ∑ l, g i l j := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

/-- The symmetrised triple sum equals the unsymmetrised one. -/
theorem sum_S3_eq_sum_Y3 (m k : ℕ) {n : ℕ} (t : Fin n → Fin n → ℝ) (hsym : ∀ i j, t j i = t i j)
    (w : Fin m → ℝ) :
    ∑ i, ∑ j, ∑ l, w ⬝ᵥ (S3 m k (t i j) (t i l) (t j l)).mulVec w
      = ∑ i, ∑ j, ∑ l, w ⬝ᵥ (Y3 m k (t i j) (t i l) (t j l)).mulVec w := by
  set Φ : Fin n → Fin n → Fin n → ℝ :=
    fun i j l => w ⬝ᵥ (Y3 m k (t i j) (t i l) (t j l)).mulVec w with hΦ
  have expand : ∀ i j l, w ⬝ᵥ (S3 m k (t i j) (t i l) (t j l)).mulVec w
      = (1 / 6 : ℝ) * (Φ i j l + Φ j i l + Φ i l j + Φ l i j + Φ j l i + Φ l j i) := by
    intro i j l
    simp only [S3, Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul, dotProduct_add,
      smul_eq_mul, hΦ, hsym]
  have e1 : ∑ i, ∑ j, ∑ l, Φ j i l = ∑ i, ∑ j, ∑ l, Φ i j l := (tsum_swap12 Φ).symm
  have e2 : ∑ i, ∑ j, ∑ l, Φ i l j = ∑ i, ∑ j, ∑ l, Φ i j l := (tsum_swap23 Φ).symm
  have e3 : ∑ i, ∑ j, ∑ l, Φ l i j = ∑ i, ∑ j, ∑ l, Φ i j l := by
    rw [tsum_swap23 (fun i j l => Φ l i j)]; exact (tsum_swap12 Φ).symm
  have e4 : ∑ i, ∑ j, ∑ l, Φ j l i = ∑ i, ∑ j, ∑ l, Φ i j l := by
    rw [tsum_swap12 (fun i j l => Φ j l i)]; exact (tsum_swap23 Φ).symm
  have e5 : ∑ i, ∑ j, ∑ l, Φ l j i = ∑ i, ∑ j, ∑ l, Φ i j l := by
    rw [tsum_swap12 (fun i j l => Φ l j i), tsum_swap23 (fun i j l => Φ l i j)]
    exact (tsum_swap12 Φ).symm
  simp only [expand, ← Finset.mul_sum, Finset.sum_add_distrib, e1, e2, e3, e4, e5]
  ring

/-- Every unit vector of `ℝ³` has an orthonormal frame of its orthogonal complement, giving
tangent-plane coordinates with Parseval's identity: extend `{x}` to an orthonormal basis. -/
theorem exists_tangent_frame (x : R3) (hx : ‖x‖ = 1) :
    ∃ e₁ e₂ : R3, ∀ y z : R3, ‖y‖ = 1 → ‖z‖ = 1 →
      (1 - ⟪x, y⟫ ^ 2 = ⟪e₁, y⟫ ^ 2 + ⟪e₂, y⟫ ^ 2) ∧
      (⟪y, z⟫ - ⟪x, y⟫ * ⟪x, z⟫ = ⟪e₁, y⟫ * ⟪e₁, z⟫ + ⟪e₂, y⟫ * ⟪e₂, z⟫) := by
  have hcard : Module.finrank ℝ R3 = Fintype.card (Fin 3) := by simp
  let v : Fin 3 → R3 := fun _ => x
  have hv : Orthonormal ℝ (({0} : Set (Fin 3)).domRestrict v) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subtype.ext (by
      have hi := i.2; have hj := j.2
      simp only [Set.mem_singleton_iff] at hi hj
      rw [hi, hj])
    subst hij
    simp [Set.domRestrict, v, real_inner_self_eq_norm_sq, hx]
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard hv
  have hb0 : b 0 = x := hb 0 (Set.mem_singleton 0)
  refine ⟨b 1, b 2, fun y z hy hz => ?_⟩
  have P := b.sum_inner_mul_inner y z
  have Py := b.sum_inner_mul_inner y y
  rw [Fin.sum_univ_three, hb0] at P Py
  rw [real_inner_self_eq_norm_sq, hy] at Py
  have c1 : ⟪y, x⟫ = ⟪x, y⟫ := real_inner_comm _ _
  have c2 : ⟪y, b 1⟫ = ⟪b 1, y⟫ := real_inner_comm _ _
  have c3 : ⟪y, b 2⟫ = ⟪b 2, y⟫ := real_inner_comm _ _
  rw [c1, c2, c3] at P Py
  constructor
  · linear_combination -Py
  · linear_combination -P

/-- **Bachoc–Vallentin positivity for `S²`.** For unit vectors `x i`, the moment matrix
`Σ_{i,j,l} S_k(⟨xᵢ,xⱼ⟩, ⟨xᵢ,x_l⟩, ⟨xⱼ,x_l⟩)` is positive semidefinite (as a quadratic form). -/
theorem bv_positivity (m k : ℕ) {n : ℕ} (x : Fin n → R3) (hx : ∀ i, ‖x i‖ = 1) (w : Fin m → ℝ) :
    0 ≤ ∑ i, ∑ j, ∑ l, w ⬝ᵥ (S3 m k ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫).mulVec w := by
  have hsym : ∀ i j, ⟪x j, x i⟫ = ⟪x i, x j⟫ := fun i j => real_inner_comm _ _
  have e := sum_S3_eq_sum_Y3 m k (fun i j => ⟪x i, x j⟫) hsym w
  beta_reduce at e
  rw [e]
  refine Finset.sum_nonneg fun i _ => ?_
  obtain ⟨e₁, e₂, hfr⟩ := exists_tangent_frame (x i) (hx i)
  exact quad_Y3_nonneg m k (fun j => ⟪x i, x j⟫)
    (fun j l => ⟪x j, x l⟫) (fun j => ⟪e₁, x j⟫) (fun j => ⟪e₂, x j⟫)
    (fun j => (hfr (x j) (x j) (hx j) (hx j)).1)
    (fun j l => (hfr (x j) (x l) (hx j) (hx l)).2) w

/- DEFFERED: the general-PSD pairing lemma
`matDot_moment_nonneg (hF : F.PosSemidef) : 0 ≤ ∑ i j l, matDot F (S3 ...)`
needs `Matrix.posSemidef_iff_eq_sum_vecMulVec` from
`Mathlib.Analysis.InnerProductSpace.Positive`, whose dependency closure
(Spectrum, Hermitian, Trace, Bernstein, Matrix/Order) is not in the pinned
cache and is too deep to compile here.  The quadratic-form positivity that
it consumes, `bv_positivity`, is proved above. -/

end ThreePoint
end ThomsonNine
