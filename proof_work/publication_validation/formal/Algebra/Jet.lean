import ThomsonNine.FixedIntervalSigned
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

noncomputable section
namespace ThomsonNine.ContactJet

abbrev Point := Fin 3 → ℝ
structure Jet where
  value : ℝ
  gradient : Fin 3 → ℝ
def Correct (f : Point → ℝ) (x : Point) (j : Jet) : Prop :=
  j.value=f x ∧ ∀ i, HasDerivAt (fun t => f (Function.update x i t)) (j.gradient i) (x i)
def constant (a : ℝ) : Jet := ⟨a,fun _ => 0⟩
def coordinate (x : Point) (i : Fin 3) : Jet := ⟨x i,fun j => if i=j then 1 else 0⟩
def add (a b : Jet) : Jet := ⟨a.value+b.value,fun i => a.gradient i+b.gradient i⟩
def neg (a : Jet) : Jet := ⟨-a.value,fun i => -a.gradient i⟩
def mul (a b : Jet) : Jet :=
  ⟨a.value*b.value,fun i => a.gradient i*b.value+a.value*b.gradient i⟩

theorem correct_constant (a : ℝ) (x : Point) : Correct (fun _ => a) x (constant a) :=
  ⟨rfl,fun i => hasDerivAt_const (x i) a⟩
theorem correct_coordinate (x : Point) (i : Fin 3) : Correct (fun y => y i) x (coordinate x i) := by
  refine ⟨rfl,?_⟩
  intro j
  by_cases h : i=j
  · subst j
    convert hasDerivAt_id' (x i) using 1 <;> simp [coordinate]
  · simpa [coordinate,h,Function.update_of_ne h] using hasDerivAt_const (x j) (x i)
theorem Correct.add {f g : Point → ℝ} {x : Point} {a b : Jet}
    (ha : Correct f x a) (hb : Correct g x b) : Correct (fun y => f y+g y) x (add a b) := by
  exact ⟨by change a.value+b.value=f x+g x; rw [ha.1,hb.1],fun i => (ha.2 i).add (hb.2 i)⟩
theorem Correct.neg {f : Point → ℝ} {x : Point} {a : Jet}
    (ha : Correct f x a) : Correct (fun y => -f y) x (neg a) := by
  exact ⟨by change -a.value= -f x; rw [ha.1],fun i => (ha.2 i).neg⟩
theorem Correct.mul {f g : Point → ℝ} {x : Point} {a b : Jet}
    (ha : Correct f x a) (hb : Correct g x b) : Correct (fun y => f y*g y) x (mul a b) := by
  refine ⟨by change a.value*b.value=f x*g x; rw [ha.1,hb.1],?_⟩
  intro i
  convert (ha.2 i).mul (hb.2 i) using 1 <;>
    simp [ContactJet.mul,ha.1,hb.1,Function.update_eq_self]

structure Input where
  value : FixedInterval.Bounds
  gradient : Fin 3 → FixedInterval.Bounds
def Mem (s : ℤ) (I : Input) (a : Jet) : Prop :=
  FixedInterval.Mem s I.value a.value ∧ ∀ i, FixedInterval.Mem s (I.gradient i) (a.gradient i)
def inputConstant (I : FixedInterval.Bounds) : Input := ⟨I,fun _ => FixedInterval.zero⟩
def inputCoordinate (s : ℤ) (x : Fin 3 → FixedInterval.Bounds) (i : Fin 3) : Input :=
  ⟨x i,fun j => if i=j then FixedInterval.constant s 1 else FixedInterval.zero⟩
def inputAdd (a b : Input) : Input :=
  ⟨FixedInterval.add a.value b.value,fun i => FixedInterval.add (a.gradient i) (b.gradient i)⟩
def inputNeg (a : Input) : Input :=
  ⟨FixedInterval.neg a.value,fun i => FixedInterval.neg (a.gradient i)⟩
def inputMul (s : ℤ) (a b : Input) : Input :=
  ⟨FixedInterval.mul s a.value b.value,fun i => FixedInterval.add
    (FixedInterval.mul s (a.gradient i) b.value) (FixedInterval.mul s a.value (b.gradient i))⟩

theorem mem_constant {s : ℤ} {I : FixedInterval.Bounds} {a : ℝ} (h : FixedInterval.Mem s I a) :
    Mem s (inputConstant I) (constant a) := ⟨h,fun _ => FixedInterval.mem_zero s⟩
theorem mem_coordinate {s : ℤ} {I : Fin 3 → FixedInterval.Bounds} {x : Point}
    (h : ∀ i, FixedInterval.Mem s (I i) (x i)) (i : Fin 3) :
    Mem s (inputCoordinate s I i) (coordinate x i) := by
  refine ⟨h i,?_⟩
  intro j
  by_cases hij : i=j
  · simpa [inputCoordinate,coordinate,hij] using FixedInterval.mem_constant s 1
  · simpa [inputCoordinate,coordinate,hij] using FixedInterval.mem_zero s
theorem mem_add {s : ℤ} {I J : Input} {a b : Jet} (ha : Mem s I a) (hb : Mem s J b) :
    Mem s (inputAdd I J) (add a b) :=
  ⟨FixedInterval.mem_add ha.1 hb.1,fun i => FixedInterval.mem_add (ha.2 i) (hb.2 i)⟩
theorem mem_neg {s : ℤ} {I : Input} {a : Jet} (ha : Mem s I a) :
    Mem s (inputNeg I) (neg a) := ⟨FixedInterval.mem_neg ha.1,fun i => FixedInterval.mem_neg (ha.2 i)⟩
theorem mem_mul {s : ℤ} (hs : 0<s) {I J : Input} {a b : Jet} (ha : Mem s I a) (hb : Mem s J b) :
    Mem s (inputMul s I J) (mul a b) :=
  ⟨FixedInterval.mem_mul hs ha.1 hb.1,fun i => FixedInterval.mem_add
    (FixedInterval.mem_mul hs (ha.2 i) hb.1) (FixedInterval.mem_mul hs ha.1 (hb.2 i))⟩
end ThomsonNine.ContactJet
