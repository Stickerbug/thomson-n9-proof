import ThomsonNine.ActualHermiteArray
import ThomsonNine.ActualQuotientStructure
import ThomsonNine.IntervalMonicSolve

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
noncomputable section
namespace ThomsonNine.ActualHermite.QuotientCoefficients
open Polynomial
open ThomsonNine.ListPolynomial
open ThomsonNine.FixedInterval
open ThomsonNine.ActualHermite.CoefficientData
open ThomsonNine.ActualHermite.QuotientStructure
open scoped BigOperators

def realLinear (i : Fin 14) : List ℝ := [-node i,1]
def fixedLinear (i : Fin 14) : List Bounds := [neg (inputNode i),constant unitScale 1]
def realSquare (i : Fin 14) := multiply 0 (·+·) (·*·) (realLinear i) (realLinear i)
def fixedSquare (i : Fin 14) := multiply zero add (mul unitScale) (fixedLinear i) (fixedLinear i)
def realW := productCoefficients 0 1 (·+·) (·*·) ((List.finRange 14).map realSquare)
def fixedW := productCoefficients zero (constant unitScale 1) add (mul unitScale)
  ((List.finRange 14).map fixedSquare)

lemma linear_mem (i : Fin 14) : List.Forall₂ (Mem unitScale) (fixedLinear i) (realLinear i) :=
  List.Forall₂.cons (mem_neg (inputNode_mem i))
    (List.Forall₂.cons (by simpa using mem_constant unitScale 1) List.Forall₂.nil)
lemma square_mem (i : Fin 14) : List.Forall₂ (Mem unitScale) (fixedSquare i) (realSquare i) :=
  mem_multiply unitScale_pos (linear_mem i) (linear_mem i)
lemma W_mem : List.Forall₂ (Mem unitScale) fixedW realW := by
  unfold fixedW realW
  exact mem_productCoefficients unitScale_pos (by simpa using mem_constant unitScale 1)
    (rel_map _ _ _ _ (fun i _ => square_mem i))
lemma square_polynomial (i : Fin 14) : polynomial (realSquare i) = (X-C (node i))^2 := by
  simp [realSquare,polynomial_multiply,realLinear,polynomial]
  ring
lemma W_polynomial : polynomial realW = W := by
  rw [realW,polynomial_productCoefficients,List.map_map]
  change ((List.finRange 14).map (fun i => polynomial (realSquare i))).prod = W
  rw [← List.prod_toFinset _ (show (List.finRange 14).Nodup by decide +kernel)]
  have heq : (List.finRange 14).toFinset = (Finset.univ : Finset (Fin 14)) := by ext i; simp
  rw [heq]
  exact Finset.prod_congr rfl (fun i _ => square_polynomial i)

def realG := zipAdd (·+·) [1]
  ((multiply 0 (·+·) (·*·) [2,-2]
    (multiply 0 (·+·) (·*·) Coefficients.realCoefficients Coefficients.realCoefficients)).map (fun x => -x))
def fixedG := zipAdd add [constant unitScale 1]
  ((multiply zero add (mul unitScale) [constant unitScale 2,constant unitScale (-2)]
    (multiply zero add (mul unitScale) Coefficients.fixedCoefficients Coefficients.fixedCoefficients)).map neg)

lemma G_mem : List.Forall₂ (Mem unitScale) fixedG realG := by
  unfold fixedG realG
  apply rel_zipAdd (Mem unitScale) add (·+·) (fun h₁ h₂ => mem_add h₁ h₂)
  · exact List.Forall₂.cons (by simpa using mem_constant unitScale 1) List.Forall₂.nil
  · apply mem_map_neg
    apply mem_multiply unitScale_pos
    · exact List.Forall₂.cons (by simpa using mem_constant unitScale 2)
        (List.Forall₂.cons (by simpa using mem_constant unitScale (-2)) List.Forall₂.nil)
    · exact mem_multiply unitScale_pos Coefficients.coefficients_mem Coefficients.coefficients_mem

lemma G_polynomial : polynomial realG = HermiteFactor.G H := by
  simp only [realG,polynomial_zipAdd,polynomial_map_neg,polynomial_multiply,
    Coefficients.coefficients_polynomial,polynomial]
  simp [HermiteFactor.G]
  ring

def w (n : ℕ) : Bounds := ((fixedW[n]?).getD zero)
def g (n : ℕ) : Bounds := ((fixedG[n]?).getD zero)
lemma w_mem (n : ℕ) : Mem unitScale (w n) (W.coeff n) := by
  simpa only [w,W_polynomial] using mem_coeff W_mem n
lemma g_mem (n : ℕ) : Mem unitScale (g n) ((HermiteFactor.G H).coeff n) := by
  simpa only [g,G_polynomial] using mem_coeff G_mem n

def fixedQ := IntervalMonicSolve.solveTail 28 unitScale g w 28
lemma Q_zero (n : ℕ) (hn : 28≤n) : Q.coeff n=0 := Q_coefficient_zero (by omega)
lemma Q_recurrence (n : ℕ) (_hn : n<28) :
    Q.coeff n = (HermiteFactor.G H).coeff (n+28)-
      ∑ j ∈ Finset.range 28, W.coeff j*Q.coeff (n+28-j) := by
  rw [QuotientStructure.factor]
  exact monic_quotient_coefficient W Q 28 W_natDegree W_monic n
lemma Q_mem : List.Forall₂ (Mem unitScale) fixedQ (IntervalMonicSolve.realTail 28 Q.coeff 28) :=
  IntervalMonicSolve.solveTail_mem 28 unitScale_pos g w _ _ _ g_mem w_mem Q_zero Q_recurrence 28 (le_refl 28)
theorem fixed_coefficient_mem (n : ℕ) :
    Mem unitScale ((fixedQ[n]?).getD zero) (Q.coeff n) := by
  have h := mem_coeff Q_mem n
  rw [IntervalMonicSolve.polynomial_realTail 28 Q Q_zero] at h
  exact h
end ThomsonNine.ActualHermite.QuotientCoefficients
