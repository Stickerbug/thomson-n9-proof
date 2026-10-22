import ThomsonNine.IntervalListPolynomial

noncomputable section
namespace ThomsonNine.IntegerListPolynomial
open Polynomial ThomsonNine.ListPolynomial
def realPolynomial (l : List ℤ) : ℝ[X] := polynomial (l.map (fun z => (z : ℝ)))
@[simp] theorem nil : realPolynomial []=0 := rfl
@[simp] theorem cons (a : ℤ) (l : List ℤ) : realPolynomial (a::l)=C (a : ℝ)+X*realPolynomial l := rfl
def add (l m : List ℤ) := zipAdd (·+·) l m
def mul (l m : List ℤ) := multiply 0 (·+·) (·*·) l m
def scale (a : ℤ) (l : List ℤ) := l.map (a*·)
def pow (l : List ℤ) : ℕ → List ℤ
  | 0 => [1]
  | n+1 => mul l (pow l n)
theorem add_sound (l m : List ℤ) : realPolynomial (add l m)=realPolynomial l+realPolynomial m := by
  induction l generalizing m with
  | nil => simp [add,zipAdd,realPolynomial,polynomial]
  | cons a l ih =>
    cases m with
    | nil => simp [add,zipAdd,realPolynomial,polynomial]
    | cons b m =>
      change C ((a+b : ℤ) : ℝ)+X*realPolynomial (add l m)=
        (C (a : ℝ)+X*realPolynomial l)+(C (b : ℝ)+X*realPolynomial m)
      rw [ih,Int.cast_add,map_add]
      ring
theorem scale_sound (a : ℤ) (l : List ℤ) : realPolynomial (scale a l)=C (a : ℝ)*realPolynomial l := by
  induction l with
  | nil => simp [scale,realPolynomial,polynomial]
  | cons b l ih =>
    change C ((a*b : ℤ) : ℝ)+X*realPolynomial (scale a l)=C (a : ℝ)*(C (b : ℝ)+X*realPolynomial l)
    rw [ih,Int.cast_mul,map_mul]
    ring
theorem mul_sound (l m : List ℤ) : realPolynomial (mul l m)=realPolynomial l*realPolynomial m := by
  induction l with
  | nil => simp [mul,multiply,realPolynomial,polynomial]
  | cons a l ih =>
    change realPolynomial (add (scale a m) (0::mul l m))=_
    rw [add_sound,scale_sound]
    rw [cons,cons,ih]
    simp only [Int.cast_zero,map_zero,zero_add]
    ring
theorem pow_sound (l : List ℤ) (n : ℕ) : realPolynomial (pow l n)=(realPolynomial l)^n := by
  induction n with
  | zero => simp [pow,realPolynomial,polynomial]
  | succ n ih => rw [pow,mul_sound,ih,pow_succ']
end ThomsonNine.IntegerListPolynomial
