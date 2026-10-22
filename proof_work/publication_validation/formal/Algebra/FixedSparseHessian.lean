import ThomsonNine.FixedIntervalSigned
import ThomsonNine.IntervalSparseDerivative

noncomputable section
namespace ThomsonNine.FixedSparseHessian
open ThomsonNine.FixedInterval ThomsonNine.Interval.SparsePolynomial

def monomialInput (s : ℤ) (P : Fin 3 → ℕ → Bounds) (e : Exp3) : Bounds :=
  mul s (mul s (P 0 (e 0)) (P 1 (e 1))) (P 2 (e 2))
def evalInput {α : Type*} (s : ℤ) (e : α → Exp3) (C : α → Bounds)
    (P : Fin 3 → ℕ → Bounds) (l : List α) : Bounds :=
  sum (l.map (fun t => mul s (C t) (monomialInput s P (e t))))

theorem monomial_mem {s : ℤ} (hs : 0<s) (P : Fin 3 → ℕ → Bounds) (x : Fin 3 → ℝ)
    (hP : ∀ i n, Mem s (P i n) ((x i)^n)) (e : Exp3) :
    Mem s (monomialInput s P e) (monomial e x) :=
  mem_mul hs (mem_mul hs (hP 0 _) (hP 1 _)) (hP 2 _)

theorem evalInput_mem {α : Type*} {s : ℤ} (hs : 0<s) (e : α → Exp3) (C : α → Bounds)
    (c : α → ℝ) (P : Fin 3 → ℕ → Bounds) (x : Fin 3 → ℝ) (l : List α)
    (hC : ∀ t∈l, Mem s (C t) (c t)) (hP : ∀ i n, Mem s (P i n) ((x i)^n)) :
    Mem s (evalInput s e C P l) (eval e c x l) := by
  induction l with
  | nil => exact mem_zero s
  | cons t l ih =>
    apply mem_add
    · exact mem_mul hs (hC t (by simp)) (monomial_mem hs P x hP (e t))
    · exact ih (fun a ha => hC a (by simp [ha]))

def hessianInput {α : Type*} (s : ℤ) (e : α → Exp3) (C : α → Bounds)
    (P : Fin 3 → ℕ → Bounds) (i j : Fin 3) (l : List α) : Bounds :=
  evalInput s (fun t => lowerExponent j (lowerExponent i (e t)))
    (fun t => scale ((e t i)*(lowerExponent i (e t) j)) (C t)) P l

theorem hessianInput_mem {α : Type*} {s : ℤ} (hs : 0<s) (e : α → Exp3) (C : α → Bounds)
    (c : α → ℝ) (P : Fin 3 → ℕ → Bounds) (x : Fin 3 → ℝ) (i j : Fin 3) (l : List α)
    (hC : ∀ t∈l, Mem s (C t) (c t)) (hP : ∀ a n, Mem s (P a n) ((x a)^n)) :
    Mem s (hessianInput s e C P i j l) (formalHessianEntry e c i j x l) := by
  apply evalInput_mem hs _ _ _ P x l _ hP
  intro t ht
  simp only [derivativeCoeff_eq_mul]
  convert mem_scale (hC t ht) ((e t i)*(lowerExponent i (e t) j)) using 1 <;>
    push_cast <;> ring
end ThomsonNine.FixedSparseHessian
