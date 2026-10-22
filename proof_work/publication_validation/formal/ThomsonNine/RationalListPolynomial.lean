import ThomsonNine.IntervalListPolynomial
import Mathlib.RingTheory.Polynomial.Bernstein

noncomputable section
namespace ThomsonNine.RationalListPolynomial
open Polynomial ThomsonNine.ListPolynomial

def realPolynomial (l : List ℚ) : ℝ[X] := polynomial (l.map (fun q => (q : ℝ)))
@[simp] theorem nil : realPolynomial []=0 := rfl
@[simp] theorem cons (a : ℚ) (l : List ℚ) :
    realPolynomial (a::l)=C (a : ℝ)+X*realPolynomial l := rfl
theorem append (l m : List ℚ) : realPolynomial (l++m) =
    realPolynomial l+X^l.length*realPolynomial m := by
  induction l with
  | nil => simp [realPolynomial,polynomial]
  | cons a l ih =>
    change C (a : ℝ)+X*realPolynomial (l++m) =
      (C (a : ℝ)+X*realPolynomial l)+X^(l.length+1)*realPolynomial m
    rw [ih,pow_succ]
    ring
theorem zeroes (n : ℕ) : realPolynomial (List.replicate n 0)=0 := by
  induction n with
  | zero => simp [realPolynomial,polynomial]
  | succ n ih => rw [List.replicate_succ,cons,ih]; simp
def unit (k : Fin 28) : List ℚ := List.replicate k 0++[1]++List.replicate (27-k) 0
theorem unit_polynomial (k : Fin 28) : realPolynomial (unit k)=X^(k : ℕ) := by
  rw [unit,append,append,zeroes,zeroes]
  simp
theorem add (l m : List ℚ) : realPolynomial (zipAdd (·+·) l m) = realPolynomial l+realPolynomial m := by
  induction l generalizing m with
  | nil => simp [zipAdd,realPolynomial,polynomial]
  | cons a l ih =>
    cases m with
    | nil => simp [zipAdd,realPolynomial,polynomial]
    | cons b m =>
      change C ((a+b : ℚ) : ℝ)+X*realPolynomial (zipAdd (·+·) l m) =
        (C (a : ℝ)+X*realPolynomial l)+(C (b : ℝ)+X*realPolynomial m)
      rw [ih,Rat.cast_add,map_add]
      ring
theorem scale (a : ℚ) (l : List ℚ) :
    realPolynomial (l.map (a*·)) = C (a : ℝ)*realPolynomial l := by
  induction l with
  | nil => simp [realPolynomial,polynomial]
  | cons b l ih =>
    change C ((a*b : ℚ) : ℝ)+X*realPolynomial (l.map (a*·)) =
      C (a : ℝ)*(C (b : ℝ)+X*realPolynomial l)
    rw [ih,Rat.cast_mul,map_mul]
    ring
theorem mul (l m : List ℚ) : realPolynomial (multiply 0 (·+·) (·*·) l m) =
    realPolynomial l*realPolynomial m := by
  induction l with
  | nil => simp [multiply,realPolynomial,polynomial]
  | cons a l ih =>
    rw [multiply,add,scale]
    rw [cons,cons,ih]
    simp
    ring

def power (l : List ℚ) : ℕ → List ℚ
  | 0 => [1]
  | n+1 => multiply 0 (·+·) (·*·) l (power l n)
theorem pow (l : List ℚ) (n : ℕ) : realPolynomial (power l n) = (realPolynomial l)^n := by
  induction n with
  | zero => simp [power,realPolynomial,polynomial]
  | succ n ih => rw [power,mul,ih,pow_succ'];

def z : List ℚ := [1/2,1/2]
def oneMinusZ : List ℚ := [1/2,-1/2]
def basis (i : Fin 28) : List ℚ :=
  (multiply 0 (·+·) (·*·) (power z i) (power oneMinusZ (27-i))).map
    (fun q => (Nat.choose 27 i : ℚ)*q)
def Z : ℝ[X] := C (1/2)* (X+1)
def B (i : Fin 28) : ℝ[X] := (bernsteinPolynomial ℝ 27 i).comp Z

theorem basis_polynomial (i : Fin 28) : realPolynomial (basis i) = B i := by
  rw [basis,scale,mul,pow,pow]
  have hz : realPolynomial z=Z := by simp [z,Z,realPolynomial,polynomial]; ring
  have hv : realPolynomial oneMinusZ=1-Z := by
    have hc : (C (1/2 : ℝ) : ℝ[X])+C (1/2 : ℝ)=1 := by rw [← map_add]; norm_num
    calc
      realPolynomial oneMinusZ = C (1/2 : ℝ)-C (1/2 : ℝ)*X := by
        simp [oneMinusZ,realPolynomial,polynomial,neg_div,sub_eq_add_neg]
      _ = (C (1/2 : ℝ)+C (1/2 : ℝ))-C (1/2 : ℝ)*(X+1) := by ring
      _ = 1-Z := by rw [hc]; rfl
  rw [hz,hv]
  simp [B,bernsteinPolynomial]
  ring

def linearCombination (weights : Fin 28 → ℚ) : List ℚ :=
  sumCoefficients (·+·) ((List.finRange 28).map (fun i => (basis i).map (weights i*·)))

theorem sum (ls : List (List ℚ)) : realPolynomial (sumCoefficients (·+·) ls) =
    (ls.map realPolynomial).sum := by
  induction ls with
  | nil => simp [sumCoefficients,realPolynomial,polynomial]
  | cons l ls ih => simp only [sumCoefficients,add,ih,List.map_cons,List.sum_cons]

theorem linearCombination_polynomial (weights : Fin 28 → ℚ) :
    realPolynomial (linearCombination weights) =
      ∑ i : Fin 28, C (weights i : ℝ)*B i := by
  rw [linearCombination,sum,List.map_map]
  change ((List.finRange 28).map (fun i => realPolynomial ((basis i).map (weights i*·)))).sum = _
  rw [← List.sum_toFinset _ (show (List.finRange 28).Nodup by decide +kernel)]
  have heq : (List.finRange 28).toFinset = (Finset.univ : Finset (Fin 28)) := by ext i; simp
  rw [heq]
  exact Finset.sum_congr rfl (fun i _ => by rw [scale,basis_polynomial])

theorem B_nonnegative (i : Fin 28) (t : ℝ) (ht : -1≤t ∧ t≤1) : 0≤(B i).eval t := by
  have hu : 0≤Z.eval t := by simp [Z]; linarith
  have hv : 0≤1-Z.eval t := by simp [Z]; linarith
  simp only [B,eval_comp,bernsteinPolynomial,eval_mul,eval_pow,eval_natCast,eval_X,eval_sub,eval_one]
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hu _)) (pow_nonneg hv _)
end ThomsonNine.RationalListPolynomial
