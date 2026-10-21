import ThomsonNine.IntervalSparsePolynomial
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fin.VecNotation

/-! Exact translation of a fixed real sparse polynomial, before collecting terms.

The real center `a` and original coefficient family `c` are fixed parameters.
The expanded coefficient depends on these and the two exponent triples, never on
its evaluation point `x`. Every original monomial is expanded over the three
finite ranges `0 <= k i <= e i`. Repeated original terms remain repeated terms.

This module does not collect equal exponents, identify the actual residual's
coefficients, replay rounded translation, compare to archived shifted intervals,
or prove contact values or gradients vanish. Interval conclusions enclose the
fixed expanded coefficients; they do not assert equality to interval endpoints.
-/

noncomputable section

namespace ThomsonNine.Interval.SparsePolynomial

open ThomsonNine.Interval.RatInterval
open scoped BigOperators

/-- An explicit exponent triple used by the three finite binomial sums. -/
def exponentTriple (k0 k1 k2 : ℕ) : Exp3 := ![k0, k1, k2]

/-- Uncollected finite binomial index sum, including both endpoints in each axis. -/
def tripleSum (e : Exp3) (f : Exp3 → ℝ) : ℝ :=
  ∑ k0 ∈ Finset.range (e 0 + 1),
    ∑ k1 ∈ Finset.range (e 1 + 1),
      ∑ k2 ∈ Finset.range (e 2 + 1), f (exponentTriple k0 k1 k2)

/-- One axis's fixed coefficient in the translation `(a + x)^n`. -/
def shiftFactor (n k : ℕ) (a : ℝ) : ℝ :=
  (n.choose k : ℝ) * a ^ (n - k)

/-- Fixed coefficient of the uncollected term of relative exponent `k` arising
from the original term `c * monomial e`. There is no dependence on `x`. -/
def expandedCoefficient (e k : Exp3) (c : ℝ) (a : Fin 3 → ℝ) : ℝ :=
  ((c * shiftFactor (e 0) (k 0) (a 0)) *
    shiftFactor (e 1) (k 1) (a 1)) * shiftFactor (e 2) (k 2) (a 2)

/-- The ordinary one-variable binomial expansion, in relative-power order. -/
theorem shifted_pow (a x : ℝ) (n : ℕ) :
    (a + x) ^ n = ∑ k ∈ Finset.range (n + 1), shiftFactor n k a * x ^ k := by
  rw [add_comm a x, add_pow]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold shiftFactor
  ring

/-- Exact three-variable translation of one monomial, with all binomial terms
retained separately. Neither signs nor domain restrictions are needed. -/
theorem monomial_shift (e : Exp3) (a x : Fin 3 → ℝ) :
    monomial e (fun i => a i + x i) =
      tripleSum e (fun k => expandedCoefficient e k 1 a * monomial k x) := by
  rw [monomial, shifted_pow, shifted_pow, shifted_pow]
  unfold tripleSum
  rw [Finset.sum_mul_sum (Finset.range (e 0 + 1)) (Finset.range (e 1 + 1))
    (fun k0 => shiftFactor (e 0) k0 (a 0) * x 0 ^ k0)
    (fun k1 => shiftFactor (e 1) k1 (a 1) * x 1 ^ k1)]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k0 _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k1 _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k2 _ => ?_)
  dsimp [expandedCoefficient, shiftFactor, monomial, exponentTriple]
  ring

/-- Exact translation of a monomial with one fixed real coefficient. -/
theorem term_shift (e : Exp3) (c : ℝ) (a x : Fin 3 → ℝ) :
    c * monomial e (fun i => a i + x i) =
      tripleSum e (fun k => expandedCoefficient e k c a * monomial k x) := by
  rw [monomial_shift e a x]
  unfold tripleSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k0 _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k1 _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k2 _ => ?_)
  dsimp [expandedCoefficient, shiftFactor, monomial, exponentTriple]
  ring

/-- Uncollected translated sparse evaluation: each original list entry supplies
its own finite binomial sum; coefficients are fixed for the whole evaluation. -/
def expandedEval {ι : Type*} (e : ι → Exp3) (c : ι → ℝ)
    (a x : Fin 3 → ℝ) : List ι → ℝ
  | [] => 0
  | i :: s =>
      tripleSum (e i) (fun k => expandedCoefficient (e i) k (c i) a * monomial k x) +
        expandedEval e c a x s

/-- Translating one fixed sparse polynomial equals its finite uncollected
binomial expansion, for every real relative point `x`. -/
theorem eval_shift {ι : Type*} (e : ι → Exp3) (c : ι → ℝ)
    (a x : Fin 3 → ℝ) (s : List ι) :
    eval e c (fun i => a i + x i) s = expandedEval e c a x s := by
  induction s with
  | nil => rfl
  | cons i s ih =>
      change c i * monomial (e i) (fun j => a j + x j) +
        eval e c (fun j => a j + x j) s =
        tripleSum (e i) (fun k => expandedCoefficient (e i) k (c i) a * monomial k x) +
          expandedEval e c a x s
      rw [term_shift, ih]

/-- Exact rational interval expression for one axis's binomial coefficient.
Center powers can be supplied by a tighter signed-power replay. -/
def shiftFactorInterval (n k : ℕ) (P : ℕ → RatInterval) : RatInterval :=
  mul (const (n.choose k : ℚ)) (P (n - k))

theorem shiftFactor_mem (n k : ℕ) (P : ℕ → RatInterval) (a : ℝ)
    (hP : ∀ m, (P m).mem (a ^ m)) :
    (shiftFactorInterval n k P).mem (shiftFactor n k a) := by
  have hN : (const (n.choose k : ℚ)).mem (n.choose k : ℝ) := by
    simpa using mem_const (n.choose k : ℚ)
  exact mem_mul hN (hP (n - k))

/-- Interval expression for one uncollected expanded coefficient. Original
coefficients and center coordinates may have arbitrary signs. -/
def expandedCoefficientInterval (e k : Exp3) (C : RatInterval)
    (P : Fin 3 → ℕ → RatInterval) : RatInterval :=
  mul (mul (mul C (shiftFactorInterval (e 0) (k 0) (P 0)))
    (shiftFactorInterval (e 1) (k 1) (P 1)))
      (shiftFactorInterval (e 2) (k 2) (P 2))

/-- Membership of one fixed expanded coefficient, independent of the relative
point. No assumption says that an interval containing zero is an exact zero. -/
theorem expandedCoefficient_mem (e k : Exp3) (C : RatInterval) (c : ℝ)
    (P : Fin 3 → ℕ → RatInterval) (a : Fin 3 → ℝ)
    (hC : C.mem c) (hP : PowerEnclosures P a) :
    (expandedCoefficientInterval e k C P).mem (expandedCoefficient e k c a) := by
  exact mem_mul (mem_mul (mem_mul hC
    (shiftFactor_mem (e 0) (k 0) (P 0) (a 0) (hP 0)))
      (shiftFactor_mem (e 1) (k 1) (P 1) (a 1) (hP 1)))
        (shiftFactor_mem (e 2) (k 2) (P 2) (a 2) (hP 2))

/-- Any signed center box supplies sufficient center-power enclosures. This
fallback may be wider than the generator's rounded cached powers. -/
theorem expandedCoefficient_mem_of_center_box (e k : Exp3) (C : RatInterval)
    (c : ℝ) (A : Fin 3 → RatInterval) (a : Fin 3 → ℝ)
    (hC : C.mem c) (ha : ∀ i, (A i).mem (a i)) :
    (expandedCoefficientInterval e k C (fun i n => powSigned (A i) n)).mem
      (expandedCoefficient e k c a) := by
  exact expandedCoefficient_mem e k C c _ a hC (powerEnclosures_powSigned A a ha)

/-- An archived interval can be used only after explicit rational endpoint
containment of the computed expanded-coefficient enclosure is established. -/
theorem expandedCoefficient_mem_of_bounds (e k : Exp3) (C K : RatInterval)
    (c : ℝ) (P : Fin 3 → ℕ → RatInterval) (a : Fin 3 → ℝ)
    (hC : C.mem c) (hP : PowerEnclosures P a)
    (hlo : K.lo ≤ (expandedCoefficientInterval e k C P).lo)
    (hhi : (expandedCoefficientInterval e k C P).hi ≤ K.hi) :
    K.mem (expandedCoefficient e k c a) := by
  exact mem_subset (expandedCoefficient_mem e k C c P a hC hP) hlo hhi


/-- Sequential interval power cache, matching the generator's repeated
multiplication by one center interval. -/
def powInterval (A : RatInterval) : ℕ → RatInterval
  | 0 => const 1
  | n + 1 => mul (powInterval A n) A

/-- Soundness of the sequential interval power cache. -/
theorem powInterval_mem (A : RatInterval) (a : ℝ) (ha : A.mem a) (n : ℕ) :
    (powInterval A n).mem (a ^ n) := by
  induction n with
  | zero => simpa [powInterval] using mem_const (1 : ℚ)
  | succ n ih =>
      rw [pow_succ]
      simpa [powInterval] using mem_mul ih ha

/-! ## One-axis grouped coefficient shifts

The generator collects equal target exponents after each coordinate shift. The
following definitions and theorem provide a soundness lemma for one such
grouped shift, using a caller-supplied power cache. They do not assert that an
archived shifted polynomial equals the translated coefficient family. -/

/-- Boolean one-axis contribution test: target exponent matches in the other
two axes and is no larger in the shifted axis. -/
def axisContribB (axis : Fin 3) (k e : Exp3) : Bool :=
  (List.finRange 3).all (fun j => if j = axis then true else e j == k j) &&
    decide (k axis ≤ e axis)

/-- Exact coefficient of target `k` produced by shifting one axis of a finite
list of interval-labelled terms. The real coefficient function `c` supplies the
exact value associated with each exponent. -/
def axisShiftCoeff (axis : Fin 3) (a : ℝ) (k : Exp3)
    (l : List (Exp3 × RatInterval)) (c : Exp3 → ℝ) : ℝ :=
  ((l.filter (fun p => axisContribB axis k p.1)).map
    (fun p => c p.1 * ((p.1 axis).choose (k axis) : ℝ) *
      a ^ (p.1 axis - k axis))).sum

/-- Interval analogue of `axisShiftCoeff`, using the generator's
`(coefficient * binomial) * power` parenthesisation. The power cache is
per-axis because the translation center is a vector. -/
def axisShiftInterval (axis : Fin 3) (P : Fin 3 → ℕ → RatInterval) (k : Exp3)
    (l : List (Exp3 × RatInterval)) : RatInterval :=
  sumIntervals (((l.filter (fun p => axisContribB axis k p.1)).map
    (fun p => mul (mul p.2 (const ((p.1 axis).choose (k axis) : ℚ)))
      (P axis (p.1 axis - k axis)))))

/-- Soundness of one grouped axis shift. -/
theorem axisShiftCoeff_mem (axis : Fin 3) (P : Fin 3 → ℕ → RatInterval) (a : ℝ)
    (k : Exp3) (l : List (Exp3 × RatInterval)) (c : Exp3 → ℝ)
    (h : ∀ p ∈ l, p.2.mem (c p.1))
    (hP : ∀ n, (P axis n).mem (a ^ n)) :
    (axisShiftInterval axis P k l).mem (axisShiftCoeff axis a k l c) := by
  let l' := l.filter (fun p => axisContribB axis k p.1)
  let pairs : List (RatInterval × ℝ) := l'.map (fun p =>
    (mul (mul p.2 (const ((p.1 axis).choose (k axis) : ℚ)))
      (P axis (p.1 axis - k axis)),
     c p.1 * ((p.1 axis).choose (k axis) : ℝ) * a ^ (p.1 axis - k axis)))
  have hpair : ∀ q ∈ pairs, q.1.mem q.2 := by
    intro q hq
    simp only [pairs, List.mem_map] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    have hp' : p ∈ l := by
      simpa [l'] using (List.mem_filter.mp hp).1
    exact mem_mul (mem_mul (h p hp')
      (by simpa using mem_const ((p.1 axis).choose (k axis) : ℚ)))
      (hP (p.1 axis - k axis))
  have hs := mem_sumIntervals pairs hpair
  have hs' : (sumIntervals (l'.map (fun p =>
      mul (mul p.2 (const ((p.1 axis).choose (k axis) : ℚ)))
        (P axis (p.1 axis - k axis))))).mem
      (l'.map (fun p => c p.1 * ((p.1 axis).choose (k axis) : ℝ) *
        a ^ (p.1 axis - k axis))).sum := by
    simpa [pairs, List.map_map, Function.comp_def] using hs
  simpa [axisShiftInterval, axisShiftCoeff, l'] using hs'

/-- Target support produced by one grouped axis shift: every exponent obtained
by lowering one coordinate of an input exponent. -/
def axisTargets (axis : Fin 3) (l : List (Exp3 × RatInterval)) : List Exp3 :=
  (l.flatMap (fun p =>
    (List.range (p.1 axis + 1)).map (fun k => Function.update p.1 axis k))).dedup

/-- One full grouped axis shift as a finite interval-labelled support. The
interval at each target is `axisShiftInterval`; equal targets are already
collected by `axisTargets`. -/
def shiftAxis (axis : Fin 3) (P : Fin 3 → ℕ → RatInterval)
    (l : List (Exp3 × RatInterval)) : List (Exp3 × RatInterval) :=
  (axisTargets axis l).map (fun k => (k, axisShiftInterval axis P k l))

/-- Exact coefficient function after one grouped axis shift. -/
def shiftAxisCoeff (axis : Fin 3) (a : ℝ)
    (l : List (Exp3 × RatInterval)) (c : Exp3 → ℝ) : Exp3 → ℝ :=
  fun k => axisShiftCoeff axis a k l c

/-- Pointwise soundness of one grouped axis shift. -/
theorem shiftAxis_mem (axis : Fin 3) (P : Fin 3 → ℕ → RatInterval) (a : ℝ)
    (l : List (Exp3 × RatInterval)) (c : Exp3 → ℝ)
    (h : ∀ p ∈ l, p.2.mem (c p.1))
    (hP : ∀ n, (P axis n).mem (a ^ n)) :
    ∀ q ∈ shiftAxis axis P l, q.2.mem (shiftAxisCoeff axis a l c q.1) := by
  intro q hq
  rw [shiftAxis, List.mem_map] at hq
  obtain ⟨k, _hk, rfl⟩ := hq
  simpa [shiftAxisCoeff] using axisShiftCoeff_mem axis P a k l c h hP

/-- Three grouped axis shifts in the generator's order `0,1,2`, with a
center vector and a per-axis power cache. -/
def shiftAxes (P : Fin 3 → ℕ → RatInterval)
    (l : List (Exp3 × RatInterval)) : List (Exp3 × RatInterval) :=
  shiftAxis 2 P (shiftAxis 1 P (shiftAxis 0 P l))

/-- Exact coefficient function after the three grouped shifts. -/
def shiftAxesCoeff (P : Fin 3 → ℕ → RatInterval) (a : Fin 3 → ℝ)
    (l : List (Exp3 × RatInterval)) (c : Exp3 → ℝ) : Exp3 → ℝ :=
  shiftAxisCoeff 2 (a 2) (shiftAxis 1 P (shiftAxis 0 P l))
    (shiftAxisCoeff 1 (a 1) (shiftAxis 0 P l)
      (shiftAxisCoeff 0 (a 0) l c))

/-- Soundness of the three grouped axis shifts: every interval in
`shiftAxes P l` contains the exact staged coefficient. -/
theorem shiftAxes_mem (P : Fin 3 → ℕ → RatInterval) (a : Fin 3 → ℝ)
    (l : List (Exp3 × RatInterval)) (c : Exp3 → ℝ)
    (h : ∀ p ∈ l, p.2.mem (c p.1))
    (hP : ∀ i n, (P i n).mem ((a i) ^ n)) :
    ∀ q ∈ shiftAxes P l, q.2.mem (shiftAxesCoeff P a l c q.1) := by
  have h0 : ∀ q ∈ shiftAxis 0 P l,
      q.2.mem (shiftAxisCoeff 0 (a 0) l c q.1) :=
    shiftAxis_mem 0 P (a 0) l c h (fun n => hP 0 n)
  have h1 : ∀ q ∈ shiftAxis 1 P (shiftAxis 0 P l),
      q.2.mem (shiftAxisCoeff 1 (a 1) (shiftAxis 0 P l)
        (shiftAxisCoeff 0 (a 0) l c) q.1) :=
    shiftAxis_mem 1 P (a 1) (shiftAxis 0 P l)
      (shiftAxisCoeff 0 (a 0) l c) h0 (fun n => hP 1 n)
  have h2 : ∀ q ∈ shiftAxis 2 P (shiftAxis 1 P (shiftAxis 0 P l)),
      q.2.mem (shiftAxisCoeff 2 (a 2) (shiftAxis 1 P (shiftAxis 0 P l))
        (shiftAxisCoeff 1 (a 1) (shiftAxis 0 P l)
          (shiftAxisCoeff 0 (a 0) l c)) q.1) :=
    shiftAxis_mem 2 P (a 2) (shiftAxis 1 P (shiftAxis 0 P l))
      (shiftAxisCoeff 1 (a 1) (shiftAxis 0 P l)
        (shiftAxisCoeff 0 (a 0) l c)) h1 (fun n => hP 2 n)
  simpa [shiftAxes, shiftAxesCoeff] using h2

/-- If a target interval family `K` contains the staged interval at every
target, it contains the exact staged coefficient. This is the bridge used to
connect the staged family to an archived coefficient interval. -/
theorem shiftAxes_mem_of_contains (P : Fin 3 → ℕ → RatInterval) (a : Fin 3 → ℝ)
    (l : List (Exp3 × RatInterval)) (c : Exp3 → ℝ)
    (h : ∀ p ∈ l, p.2.mem (c p.1))
    (hP : ∀ i n, (P i n).mem ((a i) ^ n))
    (K : Exp3 → RatInterval)
    (hlo : ∀ q ∈ shiftAxes P l, (K q.1).lo ≤ q.2.lo)
    (hhi : ∀ q ∈ shiftAxes P l, q.2.hi ≤ (K q.1).hi) :
    ∀ q ∈ shiftAxes P l, (K q.1).mem (shiftAxesCoeff P a l c q.1) := by
  intro q hq
  exact mem_subset (shiftAxes_mem P a l c h hP q hq) (hlo q hq) (hhi q hq)

end ThomsonNine.Interval.SparsePolynomial
