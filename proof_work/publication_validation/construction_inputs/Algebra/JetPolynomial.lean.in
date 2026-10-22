import ThomsonNine.Construction.Algebra.Jet
import ThomsonNine.IntervalListPolynomial
import ThomsonNine.ThreePoint

-- Isolated source: Algebra.JetPolynomial
noncomputable section
namespace ThomsonNine.ContactJet
open ThomsonNine.ListPolynomial

def sum {α : Type*} (l : List α) (f : α → Jet) : Jet := l.foldr (fun i a => add (f i) a) (constant 0)
theorem correct_sum {α : Type*} (l : List α) (f : α → Point → ℝ) (j : α → Jet) (x : Point)
    (h : ∀ i ∈ l, Correct (f i) x (j i)) : Correct (fun y => (l.map (fun i => f i y)).sum) x (sum l j) := by
  induction l with
  | nil => exact correct_constant 0 x
  | cons i l ih =>
    exact (h i (by simp)).add (ih (fun k hk => h k (by simp [hk])))
def inputSum {α : Type*} (l : List α) (f : α → Input) : Input :=
  l.foldr (fun i a => inputAdd (f i) a) (inputConstant FixedInterval.zero)
theorem mem_sum {α : Type*} {s : ℤ} (l : List α) (I : α → Input) (j : α → Jet)
    (h : ∀ i ∈ l, Mem s (I i) (j i)) : Mem s (inputSum l I) (sum l j) := by
  induction l with
  | nil => exact mem_constant (FixedInterval.mem_zero s)
  | cons i l ih => exact mem_add (h i (by simp)) (ih (fun k hk => h k (by simp [hk])))

def subtract (a b : Jet) : Jet := add a (neg b)
theorem Correct.subtract {f g : Point → ℝ} {x : Point} {a b : Jet}
    (ha : Correct f x a) (hb : Correct g x b) : Correct (fun y => f y-g y) x (subtract a b) := by
  simpa only [ContactJet.subtract,sub_eq_add_neg] using ha.add hb.neg
def horner (a : Jet) : List ℝ → Jet
  | [] => constant 0
  | b::l => add (constant b) (mul a (horner a l))
theorem correct_horner {g : Point → ℝ} {x : Point} {a : Jet} (ha : Correct g x a) (l : List ℝ) :
    Correct (fun y => (polynomial l).eval (g y)) x (horner a l) := by
  induction l with
  | nil => simpa [polynomial,horner] using correct_constant 0 x
  | cons b l ih =>
    simpa only [polynomial,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_X,horner] using
      (correct_constant b x).add (ha.mul ih)

def q (u v t : Jet) : ℕ → Jet
  | 0 => constant 1
  | 1 => subtract t (mul u v)
  | k+2 => subtract
    (mul (mul (constant 2) (subtract t (mul u v))) (q u v t (k+1)))
    (mul (mul (subtract (constant 1) (mul u u)) (subtract (constant 1) (mul v v))) (q u v t k))
theorem correct_q {fu fv ft : Point → ℝ} {x : Point} {u v t : Jet}
    (hu : Correct fu x u) (hv : Correct fv x v) (ht : Correct ft x t) (k : ℕ) :
    Correct (fun y => ThreePoint.Q3 k (fu y) (fv y) (ft y)) x (q u v t k) := by
  have both : ∀ k, Correct (fun y => ThreePoint.Q3 k (fu y) (fv y) (ft y)) x (q u v t k) ∧
      Correct (fun y => ThreePoint.Q3 (k+1) (fu y) (fv y) (ft y)) x (q u v t (k+1)) := by
    intro k
    induction k with
    | zero => exact ⟨correct_constant 1 x,ht.subtract (hu.mul hv)⟩
    | succ k ih =>
      refine ⟨ih.2,?_⟩
      have h := (((correct_constant 2 x).mul (ht.subtract (hu.mul hv))).mul ih.2).subtract
        ((((correct_constant 1 x).subtract (hu.mul hu)).mul
          ((correct_constant 1 x).subtract (hv.mul hv))).mul ih.1)
      simpa only [q,ThreePoint.Q3,pow_two] using h
  exact (both k).1

def inputSubtract (a b : Input) : Input := inputAdd a (inputNeg b)
theorem mem_subtract {s : ℤ} {I J : Input} {a b : Jet} (ha : Mem s I a) (hb : Mem s J b) :
    Mem s (inputSubtract I J) (subtract a b) := mem_add ha (mem_neg hb)
def inputHorner (s : ℤ) (a : Input) : List FixedInterval.Bounds → Input
  | [] => inputConstant FixedInterval.zero
  | b::l => inputAdd (inputConstant b) (inputMul s a (inputHorner s a l))
theorem mem_horner {s : ℤ} (hs : 0<s) {I : Input} {a : Jet} (ha : Mem s I a)
    {l : List FixedInterval.Bounds} {m : List ℝ} (h : List.Forall₂ (FixedInterval.Mem s) l m) :
    Mem s (inputHorner s I l) (horner a m) := by
  induction h with
  | nil => exact mem_constant (FixedInterval.mem_zero s)
  | cons hb htail ih => exact mem_add (mem_constant hb) (mem_mul hs ha ih)
def inputQ (s : ℤ) (u v t : Input) : ℕ → Input
  | 0 => inputConstant (FixedInterval.constant s 1)
  | 1 => inputSubtract t (inputMul s u v)
  | k+2 => inputSubtract
    (inputMul s (inputMul s (inputConstant (FixedInterval.constant s 2)) (inputSubtract t (inputMul s u v))) (inputQ s u v t (k+1)))
    (inputMul s (inputMul s (inputSubtract (inputConstant (FixedInterval.constant s 1)) (inputMul s u u))
      (inputSubtract (inputConstant (FixedInterval.constant s 1)) (inputMul s v v))) (inputQ s u v t k))
theorem mem_q {s : ℤ} (hs : 0<s) {U V T : Input} {u v t : Jet}
    (hu : Mem s U u) (hv : Mem s V v) (ht : Mem s T t) (k : ℕ) :
    Mem s (inputQ s U V T k) (q u v t k) := by
  have hc1 : Mem s (inputConstant (FixedInterval.constant s 1)) (constant 1) := by
    simpa using mem_constant (FixedInterval.mem_constant s 1)
  have hc2 : Mem s (inputConstant (FixedInterval.constant s 2)) (constant 2) := by
    simpa using mem_constant (FixedInterval.mem_constant s 2)
  have both : ∀ k, Mem s (inputQ s U V T k) (q u v t k) ∧
      Mem s (inputQ s U V T (k+1)) (q u v t (k+1)) := by
    intro k
    induction k with
    | zero => exact ⟨hc1,mem_subtract ht (mem_mul hs hu hv)⟩
    | succ k ih =>
      exact ⟨ih.2,mem_subtract
        (mem_mul hs (mem_mul hs hc2 (mem_subtract ht (mem_mul hs hu hv))) ih.2)
        (mem_mul hs (mem_mul hs (mem_subtract hc1 (mem_mul hs hu hu))
          (mem_subtract hc1 (mem_mul hs hv hv))) ih.1)⟩
  exact (both k).1
end ThomsonNine.ContactJet
