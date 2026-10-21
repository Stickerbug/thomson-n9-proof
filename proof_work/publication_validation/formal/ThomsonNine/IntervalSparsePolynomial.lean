import ThomsonNine.IntervalLocalOps
import ThomsonNine.IntervalSum

/-! Sparse power-polynomial interval evaluation, independent of local certificate data.

A finite list indexes terms; each index has an exponent triple and one fixed real
coefficient. Repeated indices/monomials are allowed and mean repeated summands.
Power enclosures are supplied explicitly, allowing the square-based cached powers
of the Python generator to be justified separately. No sign restriction is made
on the real variables or coefficient intervals.

`formalDerivative` and `formalHessianEntry` evaluate the explicit guarded monomial
rules for formal differentiation. This file does NOT prove that these expressions
are analytic derivatives (`HasDerivAt`, `fderiv`, etc.). It also does not bind any
coefficient to the actual residual, prove a translation identity, replay Python's
640-bit rounding, or assert membership in any archived `target_Hessian` interval.
Those remain separate obligations. In particular, no contact equality follows
from a coefficient interval containing zero.
-/

noncomputable section

namespace ThomsonNine.Interval.SparsePolynomial

open ThomsonNine.Interval.RatInterval

/-- Exponent triples, in the generator's coordinate order `(u,v,t)`. -/
abbrev Exp3 := Fin 3 → ℕ

/-- Real value of one power monomial, with multiplication in coordinate order. -/
def monomial (e : Exp3) (x : Fin 3 → ℝ) : ℝ :=
  x 0 ^ e 0 * x 1 ^ e 1 * x 2 ^ e 2

/-- Caller-supplied bounds for every coordinate power. These are real membership
premises, not flags claiming that a Python computation passed. -/
def PowerEnclosures (P : Fin 3 → ℕ → RatInterval) (x : Fin 3 → ℝ) : Prop :=
  ∀ i n, (P i n).mem (x i ^ n)

/-- A simple signed-power fallback. This may be wider than the generator's
square-based cache; no equality with that cache is claimed. -/
def powSigned (I : RatInterval) : ℕ → RatInterval
  | 0 => const 1
  | n + 1 => mul (powSigned I n) I

theorem mem_powSigned {I : RatInterval} {x : ℝ} (hx : I.mem x) (n : ℕ) :
    (powSigned I n).mem (x ^ n) := by
  induction n with
  | zero => simpa [powSigned] using mem_const (1 : ℚ)
  | succ n ih =>
      simpa only [powSigned, pow_succ] using mem_mul ih hx

/-- Any signed coordinate box supplies a valid (possibly wide) power table. -/
theorem powerEnclosures_powSigned (I : Fin 3 → RatInterval) (x : Fin 3 → ℝ)
    (hx : ∀ i, (I i).mem (x i)) :
    PowerEnclosures (fun i n => powSigned (I i) n) x := by
  intro i n
  exact mem_powSigned (hx i) n

/-- Interval monomial evaluation using supplied power enclosures. -/
def monomialInterval (e : Exp3) (P : Fin 3 → ℕ → RatInterval) : RatInterval :=
  mul (mul (P 0 (e 0)) (P 1 (e 1))) (P 2 (e 2))

theorem monomial_mem (e : Exp3) (P : Fin 3 → ℕ → RatInterval)
    (x : Fin 3 → ℝ) (hP : PowerEnclosures P x) :
    (monomialInterval e P).mem (monomial e x) := by
  exact mem_mul (mem_mul (hP 0 (e 0)) (hP 1 (e 1))) (hP 2 (e 2))

/-- Sparse polynomial value. The coefficient family is fixed throughout evaluation. -/
def eval {ι : Type*} (e : ι → Exp3) (c : ι → ℝ) (x : Fin 3 → ℝ) :
    List ι → ℝ
  | [] => 0
  | k :: ks => c k * monomial (e k) x + eval e c x ks

/-- Coefficient/monomial interval products, summed with exact rational endpoints. -/
def evalInterval {ι : Type*} (e : ι → Exp3) (C : ι → RatInterval)
    (P : Fin 3 → ℕ → RatInterval) (s : List ι) : RatInterval :=
  sumIntervals (s.map (fun k => mul (C k) (monomialInterval (e k) P)))

/-- The generic sparse evaluator encloses every fixed real coefficient family
with the stated memberships, for every supplied signed power enclosure table. -/
theorem eval_mem {ι : Type*} (e : ι → Exp3) (C : ι → RatInterval)
    (c : ι → ℝ) (P : Fin 3 → ℕ → RatInterval) (x : Fin 3 → ℝ)
    (hC : ∀ k, (C k).mem (c k)) (hP : PowerEnclosures P x) (s : List ι) :
    (evalInterval e C P s).mem (eval e c x s) := by
  induction s with
  | nil =>
      change (const 0).mem (0 : ℝ)
      simpa using mem_const (0 : ℚ)
  | cons k ks ih =>
      change (add (mul (C k) (monomialInterval (e k) P))
        (evalInterval e C P ks)).mem
        (c k * monomial (e k) x + eval e c x ks)
      exact mem_add (mem_mul (hC k) (monomial_mem (e k) P x hP)) ih

/-- Lower one exponent using natural subtraction. The coefficient guard below
makes the zero-exponent case vanish rather than interpreting a negative power. -/
def lowerExponent (axis : Fin 3) (e : Exp3) : Exp3 :=
  fun i => if i = axis then e i - 1 else e i

/-- Formal derivative coefficient; constant terms vanish explicitly. -/
def derivativeCoeff (axis : Fin 3) (e : Exp3) (a : ℝ) : ℝ :=
  if e axis = 0 then 0 else a * (e axis : ℝ)

/-- Interval counterpart of the same guarded coefficient rule. -/
def derivativeCoeffInterval (axis : Fin 3) (e : Exp3) (A : RatInterval) :
    RatInterval :=
  if e axis = 0 then const 0 else mul A (const (e axis : ℚ))

theorem derivativeCoeff_mem (axis : Fin 3) (e : Exp3) {A : RatInterval}
    {a : ℝ} (ha : A.mem a) :
    (derivativeCoeffInterval axis e A).mem (derivativeCoeff axis e a) := by
  by_cases hz : e axis = 0
  · simpa [derivativeCoeffInterval, derivativeCoeff, hz] using
      mem_const (0 : ℚ)
  · have hn : (const (e axis : ℚ)).mem (e axis : ℝ) := by
      simpa using mem_const (e axis : ℚ)
    simpa only [derivativeCoeffInterval, derivativeCoeff, if_neg hz] using
      mem_mul ha hn

/-- Evaluation of the formal first derivative, with the zero guard retained. -/
def formalDerivative {ι : Type*} (e : ι → Exp3) (c : ι → ℝ)
    (axis : Fin 3) (x : Fin 3 → ℝ) (s : List ι) : ℝ :=
  eval (fun k => lowerExponent axis (e k))
    (fun k => derivativeCoeff axis (e k) (c k)) x s

def formalDerivativeInterval {ι : Type*} (e : ι → Exp3)
    (C : ι → RatInterval) (axis : Fin 3)
    (P : Fin 3 → ℕ → RatInterval) (s : List ι) : RatInterval :=
  evalInterval (fun k => lowerExponent axis (e k))
    (fun k => derivativeCoeffInterval axis (e k) (C k)) P s

theorem formalDerivative_mem {ι : Type*} (e : ι → Exp3)
    (C : ι → RatInterval) (c : ι → ℝ) (axis : Fin 3)
    (P : Fin 3 → ℕ → RatInterval) (x : Fin 3 → ℝ)
    (hC : ∀ k, (C k).mem (c k)) (hP : PowerEnclosures P x) (s : List ι) :
    (formalDerivativeInterval e C axis P s).mem
      (formalDerivative e c axis x s) := by
  exact eval_mem _ _ _ P x (fun k => derivativeCoeff_mem axis (e k) (hC k)) hP s

/-- Apply the guarded derivative rule first in `i`, then in `j`. If `i = j`,
the second guard tests the already lowered exponent, so degree-one terms vanish.
This is a formal polynomial Hessian entry, not an asserted analytic derivative. -/
def formalHessianEntry {ι : Type*} (e : ι → Exp3) (c : ι → ℝ)
    (i j : Fin 3) (x : Fin 3 → ℝ) (s : List ι) : ℝ :=
  formalDerivative (fun k => lowerExponent i (e k))
    (fun k => derivativeCoeff i (e k) (c k)) j x s

def formalHessianInterval {ι : Type*} (e : ι → Exp3)
    (C : ι → RatInterval) (i j : Fin 3)
    (P : Fin 3 → ℕ → RatInterval) (s : List ι) : RatInterval :=
  formalDerivativeInterval (fun k => lowerExponent i (e k))
    (fun k => derivativeCoeffInterval i (e k) (C k)) j P s

theorem formalHessianEntry_mem {ι : Type*} (e : ι → Exp3)
    (C : ι → RatInterval) (c : ι → ℝ) (i j : Fin 3)
    (P : Fin 3 → ℕ → RatInterval) (x : Fin 3 → ℝ)
    (hC : ∀ k, (C k).mem (c k)) (hP : PowerEnclosures P x) (s : List ι) :
    (formalHessianInterval e C i j P s).mem
      (formalHessianEntry e c i j x s) := by
  exact formalDerivative_mem _ _ _ j P x
    (fun k => derivativeCoeff_mem i (e k) (hC k)) hP s

/-- Interface for a saved Hessian endpoint pair: its containment of the exact
rational evaluator is an explicit checked premise, never inferred from a hash. -/
theorem formalHessianEntry_mem_of_bounds {ι : Type*} (e : ι → Exp3)
    (C : ι → RatInterval) (c : ι → ℝ) (i j : Fin 3)
    (P : Fin 3 → ℕ → RatInterval) (x : Fin 3 → ℝ)
    (hC : ∀ k, (C k).mem (c k)) (hP : PowerEnclosures P x) (s : List ι)
    (K : RatInterval) (hlo : K.lo ≤ (formalHessianInterval e C i j P s).lo)
    (hhi : (formalHessianInterval e C i j P s).hi ≤ K.hi) :
    K.mem (formalHessianEntry e c i j x s) := by
  exact mem_subset (formalHessianEntry_mem e C c i j P x hC hP s) hlo hhi

end ThomsonNine.Interval.SparsePolynomial
