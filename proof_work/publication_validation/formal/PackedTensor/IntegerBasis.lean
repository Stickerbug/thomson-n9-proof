import PackedTensor.BernsteinList
import Algebra.IntegerPolynomialExtra
import Algebra.FiniteIntegerPolynomial

noncomputable section
namespace ThomsonNine.PackedTensor
open Polynomial
open scoped BigOperators

def integerBasis (n i : ℕ) : List ℤ :=
  IntegerListPolynomial.scale (n.choose i : ℤ)
    (List.replicate i 0++IntegerListPolynomial.pow [1,-1] (n-i))

theorem integerBasis_polynomial (n i : ℕ) :
    IntegerListPolynomial.realPolynomial (integerBasis n i)=bernsteinPolynomial ℝ n i := by
  have h1 : IntegerListPolynomial.realPolynomial [1,-1]=(1 : ℝ[X])-X := by
    simp [IntegerListPolynomial.realPolynomial,ListPolynomial.polynomial];ring
  rw [integerBasis,IntegerListPolynomial.scale_sound,IntegerListPolynomial.append,
    IntegerListPolynomial.zeroes,IntegerListPolynomial.pow_sound,h1]
  simp only [List.length_replicate,zero_add,Int.cast_natCast,bernsteinPolynomial,C_eq_natCast]
  ring

def integerSum : List (List ℤ) → List ℤ
  | [] => []
  | x::xs => IntegerListPolynomial.add x (integerSum xs)

theorem integerSum_polynomial (l : List (List ℤ)) :
    IntegerListPolynomial.realPolynomial (integerSum l)=(l.map IntegerListPolynomial.realPolynomial).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [integerSum,IntegerListPolynomial.add_sound,ih];rfl

def integerCombination (n : ℕ) (c : Fin (n+1) → ℤ) : List ℤ :=
  integerSum ((List.finRange (n+1)).map (fun i => IntegerListPolynomial.scale (c i) (integerBasis n i.val)))

theorem integerCombination_polynomial (n : ℕ) (c : Fin (n+1) → ℤ) :
    IntegerListPolynomial.realPolynomial (integerCombination n c)=
      ∑ i, C (c i : ℝ)*bernsteinPolynomial ℝ n i.val := by
  rw [integerCombination,integerSum_polynomial,List.map_map]
  simp_rw [Function.comp_def,IntegerListPolynomial.scale_sound,integerBasis_polynomial]
  rw [← List.sum_toFinset _ (List.nodup_finRange (n+1))]
  have hs : (List.finRange (n+1)).toFinset=(Finset.univ : Finset (Fin (n+1))) := by ext i;simp
  rw [hs]

theorem integer_ofFn_eval (d : ℕ) (c : Fin d → ℤ) (s : ℝ) :
    (IntegerListPolynomial.realPolynomial (List.ofFn c)).eval s=∑ i, (c i : ℝ)*s^i.val := by
  have hlen : (List.ofFn c).length≤d := by simp
  have he := IntegerListPolynomial.eval_fin_sum d (List.ofFn c) hlen s
  have hi (i : Fin d) : (((List.ofFn c)[i.val]?).getD 0 : ℤ)=c i := by
    have hh : i.val<(List.ofFn c).length := by simpa using i.isLt
    rw [List.getElem?_eq_getElem hh]
    simp
  simpa only [hi] using he

theorem integerCombination_eval (n : ℕ) (c : Fin (n+1) → ℤ) (s : ℝ) :
    (IntegerListPolynomial.realPolynomial (integerCombination n c)).eval s=
      curve n (fun i => (c i : ℝ)) s := by
  rw [integerCombination_polynomial]
  simp only [curve,eval_finsetSum,eval_mul,eval_C,basis_eval]
end ThomsonNine.PackedTensor
