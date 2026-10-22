import MainCoverage.AxisAlgebra
import MainCoverage.LeafSemantics
import MainCoverage.DyadicGeometry

noncomputable section
namespace ThomsonNine.PackedMain
open scoped BigOperators
open ThomsonNine.PackedTensor ThomsonNine.PackedRadix ThomsonNine.MainAxis

structure AxisWitness where
  num : ℕ
  af : Fin 11 → ℤ
  ad : Fin 21 → ℤ
  bern : Fin 11 → ℚ

def leftQ (e : AxisEntry) : ℚ := -1+(39/25 : ℚ)*e.index/(1 <<< e.level : ℕ)
def rightQ (e : AxisEntry) : ℚ := leftQ e+(39/25 : ℚ)/(1 <<< e.level : ℕ)
def lambdaQ (e : AxisEntry) : ℚ := (rightQ e-leftQ e)/(1-leftQ e)
def qPoint (e : AxisEntry) (t : ℝ) : ℝ := (leftQ e : ℝ)+((rightQ e : ℝ)-(leftQ e : ℝ))*t
def upperCoefficients (word : ℕ) (i : Fin 21) : ℤ := (offset : ℤ)-(limb 128 word i.val : ℤ)
def hCoefficients (e : AxisEntry) (i : Fin 11) : ℤ := (limb 128 e.word i.val : ℤ)-(offset : ℤ)
def witnessTail (w : AxisWitness) : ℤ := ∑ j : Fin 10, max (w.ad (Fin.natAdd 11 j)) 0
def witnessQ (w : AxisWitness) (i : Fin 11) : ℤ :=
  w.af i-w.ad (Fin.castAdd 10 i)-(if i=0 then witnessTail w else 0)

def axisCertificateOK (e : AxisEntry) (word : ℕ) (w : AxisWitness) : Bool := decide (
  leftQ e<rightQ e ∧ rightQ e<1 ∧ 0≤lambdaQ e ∧
  (2-2*leftQ e)*(w.num : ℚ)^2≤(scale : ℚ)^2 ∧
  (∀ k : Fin 11, (w.af k : ℚ)≤(w.num : ℚ)*taylorCoefficient k*(lambdaQ e)^k.val) ∧
  integerCombination 20 (upperCoefficients word)=List.ofFn w.ad ∧
  exactCombination 10 w.bern=ThomsonNine.ExactPolynomial.trim ((List.ofFn (witnessQ w)).map (fun z : ℤ => (z : ℚ))) ∧
  (∀ i : Fin 11, (hCoefficients e i : ℚ)≤w.bern i))

theorem qPoint_eq (e : AxisEntry) (t : ℝ) : qPoint e t=point e.level e.index t := by
  simp [qPoint,leftQ,rightQ,point,left,width,Nat.shiftLeft_eq]

theorem witnessQ_cast (w : AxisWitness) :
    (fun i => (witnessQ w i : ℝ))=truncated (fun i => (w.af i : ℝ)) (fun i => (w.ad i : ℝ)) := by
  funext i
  simp only [witnessQ,truncated,Int.cast_sub]
  congr 1
  split_ifs
  · simp [witnessTail,tail]
  · simp

theorem diagonal_identity (word : ℕ) (w : AxisWitness)
    (h : integerCombination 20 (upperCoefficients word)=List.ofFn w.ad) (t : ℝ) :
    curve 20 (fun i => (upperCoefficients word i : ℝ)) t=powers 21 (fun i => (w.ad i : ℝ)) t := by
  have hp := congrArg (fun l => (ThomsonNine.IntegerListPolynomial.realPolynomial l).eval t) h
  simpa only [integerCombination_eval,integer_ofFn_eval,powers] using hp

theorem q_identity (w : AxisWitness)
    (h : exactCombination 10 w.bern=ThomsonNine.ExactPolynomial.trim ((List.ofFn (witnessQ w)).map (fun z : ℤ => (z : ℚ)))) (t : ℝ) :
    curve 10 (fun i => (w.bern i : ℝ)) t=powers 11 (fun i => (witnessQ w i : ℝ)) t := by
  have hp := congrArg (fun l => (ThomsonNine.RationalListPolynomial.realPolynomial l).eval t) h
  rw [exactCombination_polynomial,ThomsonNine.ExactPolynomial.trim_sound,
    ThomsonNine.IntegerListPolynomial.rational_map,integer_ofFn_eval] at hp
  simpa only [curve,powers,Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_C,basis_eval] using hp
end ThomsonNine.PackedMain
