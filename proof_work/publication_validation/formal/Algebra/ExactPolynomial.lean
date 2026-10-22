import ThomsonNine.RationalListPolynomial
import Algebra.MonomialSymmetry

set_option maxRecDepth 100000
noncomputable section
namespace ThomsonNine.ExactPolynomial
open ThomsonNine.ListPolynomial ThomsonNine.RationalListPolynomial Polynomial

def trim : List ℚ → List ℚ
  | [] => []
  | a::l => let t := trim l; if a=0 ∧ t=[] then [] else a::t
theorem trim_sound (l : List ℚ) : realPolynomial (trim l)=realPolynomial l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [trim]
    split_ifs with h
    · have hz : realPolynomial l=0 := by rw [← ih,h.2]; rfl
      simp [h.1,hz]
    · rw [cons,ih,cons]

def add (l m : List ℚ) := trim (zipAdd (·+·) l m)
def neg (l : List ℚ) := trim (l.map (-·))
def scale (a : ℚ) (l : List ℚ) := trim (l.map (a*·))
def mul (l m : List ℚ) := trim (multiply 0 (·+·) (·*·) l m)
def sub (l m : List ℚ) := add l (neg m)
def pow (l : List ℚ) : ℕ → List ℚ
  | 0 => [1]
  | n+1 => mul l (pow l n)
def sum (l : List (List ℚ)) := trim (sumCoefficients (·+·) l)

theorem add_sound (l m : List ℚ) : realPolynomial (add l m)=realPolynomial l+realPolynomial m := by
  rw [add,trim_sound,RationalListPolynomial.add]
theorem mul_sound (l m : List ℚ) : realPolynomial (mul l m)=realPolynomial l*realPolynomial m := by
  rw [mul,trim_sound,RationalListPolynomial.mul]
theorem scale_sound (a : ℚ) (l : List ℚ) : realPolynomial (scale a l)=C (a : ℝ)*realPolynomial l := by
  rw [scale,trim_sound,RationalListPolynomial.scale]
theorem neg_sound (l : List ℚ) : realPolynomial (neg l)= -realPolynomial l := by
  have he : neg l=scale (-1) l := by simp [neg,scale]
  rw [he,scale_sound]
  simp
theorem sub_sound (l m : List ℚ) : realPolynomial (sub l m)=realPolynomial l-realPolynomial m := by
  rw [sub,add_sound,neg_sound,sub_eq_add_neg]
theorem pow_sound (l : List ℚ) (n : ℕ) : realPolynomial (pow l n)=(realPolynomial l)^n := by
  induction n with
  | zero => simp [pow,realPolynomial,polynomial]
  | succ n ih => rw [pow,mul_sound,ih,pow_succ']
theorem sum_sound (l : List (List ℚ)) : realPolynomial (sum l)=(l.map realPolynomial).sum := by
  rw [sum,trim_sound,RationalListPolynomial.sum]

def q (u v t : List ℚ) : ℕ → List ℚ
  | 0 => [1]
  | 1 => sub t (mul u v)
  | n+2 => sub (scale 2 (mul (sub t (mul u v)) (q u v t (n+1))))
      (mul (mul (sub [1] (pow u 2)) (sub [1] (pow v 2))) (q u v t n))

theorem q_eval (u v t : List ℚ) (n : ℕ) (r : ℝ) :
    (realPolynomial (q u v t n)).eval r =
      ThreePoint.Q3 n ((realPolynomial u).eval r) ((realPolynomial v).eval r) ((realPolynomial t).eval r) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [q,ThreePoint.Q3,realPolynomial,polynomial]
  | one => simp [q,ThreePoint.Q3,sub_sound,mul_sound]
  | more n ih ih' =>
    simp only [q,sub_sound,mul_sound,scale_sound,pow_sound,eval_sub,eval_mul,eval_C,eval_pow]
    simp only [show realPolynomial [1]=1 by simp [realPolynomial,polynomial],eval_one]
    rw [ih,ih']
    norm_num only [Rat.cast_ofNat]
    rw [ThreePoint.Q3]
    ring
end ThomsonNine.ExactPolynomial
