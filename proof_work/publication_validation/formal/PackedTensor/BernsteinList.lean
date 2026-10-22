import PackedTensor.BernsteinModel
import Algebra.ExactComposition
import Mathlib.RingTheory.Polynomial.Bernstein

noncomputable section
namespace ThomsonNine.PackedTensor
open Polynomial ThomsonNine.RationalListPolynomial
open scoped BigOperators

def exactBasis (n i : ℕ) : List ℚ :=
  ExactPolynomial.scale (n.choose i : ℚ)
    (ExactPolynomial.mul (ExactPolynomial.pow [0,1] i) (ExactPolynomial.pow [1,-1] (n-i)))

theorem exactBasis_polynomial (n i : ℕ) : realPolynomial (exactBasis n i)=bernsteinPolynomial ℝ n i := by
  have hX : realPolynomial [0,1]=(X : ℝ[X]) := by simp
  have h1 : realPolynomial [1,-1]=(1 : ℝ[X])-X := by simp;ring
  rw [exactBasis,ExactPolynomial.scale_sound,ExactPolynomial.mul_sound,
    ExactPolynomial.pow_sound,ExactPolynomial.pow_sound,hX,h1]
  simp [bernsteinPolynomial,mul_assoc]

theorem basis_eval (n i : ℕ) (s : ℝ) : (bernsteinPolynomial ℝ n i).eval s=Semantics.bernstein n i s := by
  simp [bernsteinPolynomial,Semantics.bernstein]

def exactCombination (n : ℕ) (c : Fin (n+1) → ℚ) : List ℚ :=
  ExactPolynomial.sum ((List.finRange (n+1)).map (fun i => ExactPolynomial.scale (c i) (exactBasis n i.val)))

theorem exactCombination_polynomial (n : ℕ) (c : Fin (n+1) → ℚ) :
    realPolynomial (exactCombination n c)=∑ i, C (c i : ℝ)*bernsteinPolynomial ℝ n i.val := by
  rw [exactCombination,ExactPolynomial.sum_sound,List.map_map]
  simp_rw [Function.comp_def,ExactPolynomial.scale_sound,exactBasis_polynomial]
  rw [← List.sum_toFinset _ (List.nodup_finRange (n+1))]
  have hs : (List.finRange (n+1)).toFinset=(Finset.univ : Finset (Fin (n+1))) := by ext i;simp
  rw [hs]

def exactBasisSpec (n : ℕ) : Prop := ∀ j : Fin (n+1),
  exactCombination n (fun i => weight i.val 0 j.val)=ExactPolynomial.compose (exactBasis n j.val) [0,1/2] ∧
  exactCombination n (fun i => weight (n-i.val) i.val j.val)=ExactPolynomial.compose (exactBasis n j.val) [1/2,1/2]
instance (n : ℕ) : Decidable (exactBasisSpec n) := inferInstanceAs (Decidable (∀ _ : Fin (n+1), _ ∧ _))

theorem exactBasisSpec_sound (n : ℕ) (h : exactBasisSpec n) : basisSpec n := by
  have hleft : realPolynomial [0,1/2]=C (1/2)*X := by simp
  have hright : realPolynomial [1/2,1/2]=C (1/2)+C (1/2)*X := by simp
  constructor
  · intro j s
    have hp := congrArg realPolynomial (h j).1
    rw [exactCombination_polynomial,ExactPolynomial.compose_sound,exactBasis_polynomial,hleft] at hp
    have he := congrArg (fun p : ℝ[X] => p.eval s) hp
    simp only [eval_finsetSum,eval_mul,eval_C,eval_comp,eval_X,basis_eval] at he
    convert he using 1 <;> congr 1 <;> ring
  · intro j s
    have hp := congrArg realPolynomial (h j).2
    rw [exactCombination_polynomial,ExactPolynomial.compose_sound,exactBasis_polynomial,hright] at hp
    have he := congrArg (fun p : ℝ[X] => p.eval s) hp
    simp only [eval_finsetSum,eval_mul,eval_C,eval_comp,eval_add,eval_X,basis_eval] at he
    convert he using 1 <;> congr 1 <;> ring
end ThomsonNine.PackedTensor
