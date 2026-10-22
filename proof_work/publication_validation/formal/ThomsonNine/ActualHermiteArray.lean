import ThomsonNine.ActualHermiteScalar

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
noncomputable section
namespace ThomsonNine.ActualHermite.Coefficients
open Polynomial
open ThomsonNine.ListPolynomial
open ThomsonNine.FixedInterval
open ThomsonNine.ActualHermite.CoefficientData

abbrev Index := Fin 14

def others (i : Index) : List Index := (List.finRange 14).filter (fun j => decide (j≠i))

lemma others_ne {i j : Index} (h : j ∈ others i) : i≠j := by
  exact Ne.symm (of_decide_eq_true (List.mem_filter.mp h).2)
lemma others_nodup (i : Index) : (others i).Nodup := by
  exact (show (List.finRange 14).Nodup by decide +kernel).filter _
lemma others_finset (i : Index) : (others i).toFinset = Finset.univ.erase i := by
  ext j
  simp [others,ne_comm]

def inverse (i j : Index) : ℝ := (node i-node j)⁻¹

def linearBasis (i j : Index) : List ℝ := [-node j*inverse i j,inverse i j]
def fixedLinearBasis (i j : Index) : List Bounds :=
  [mul unitScale (neg (inputNode j)) (inputInverse i j),inputInverse i j]

def realBasis (i : Index) : List ℝ :=
  productCoefficients 0 1 (·+·) (·*·) ((others i).map (linearBasis i))
def fixedBasis (i : Index) : List Bounds :=
  productCoefficients zero (constant unitScale 1) add (mul unitScale)
    ((others i).map (fixedLinearBasis i))

lemma linearBasis_polynomial (i j : Index) :
    polynomial (linearBasis i j) = Lagrange.basisDivisor (node i) (node j) := by
  simp [linearBasis,polynomial,Lagrange.basisDivisor,inverse]
  ring

lemma basis_polynomial (i : Index) :
    polynomial (realBasis i) = HermiteInterpolation.basis node i := by
  rw [realBasis,polynomial_productCoefficients,List.map_map]
  simp only [Function.comp_def,linearBasis_polynomial]
  rw [← List.prod_toFinset _ (others_nodup i),others_finset]
  rfl

lemma linearBasis_mem (i j : Index) (h : i≠j) :
    List.Forall₂ (Mem unitScale) (fixedLinearBasis i j) (linearBasis i j) := by
  exact List.Forall₂.cons (mem_mul unitScale_pos (mem_neg (inputNode_mem j)) (inputInverse_mem i j h))
    (List.Forall₂.cons (inputInverse_mem i j h) List.Forall₂.nil)

lemma basis_mem (i : Index) : List.Forall₂ (Mem unitScale) (fixedBasis i) (realBasis i) := by
  apply mem_productCoefficients unitScale_pos (by simpa using mem_constant unitScale 1)
  apply rel_map
  intro j hj
  exact linearBasis_mem i j (others_ne hj)

def realSlope (i : Index) : ℝ := ((others i).map (inverse i)).sum
def fixedSlope (i : Index) : Bounds := FixedInterval.sum ((others i).map (inputInverse i))

lemma slope_eq_derivative (i : Index) :
    realSlope i = (HermiteInterpolation.basis node i).derivative.eval (node i) := by
  rw [realSlope,← List.sum_toFinset _ (others_nodup i),others_finset]
  exact (HermiteInterpolation.basis_derivative_at_node node node_injective i).symm

lemma slope_mem (i : Index) : Mem unitScale (fixedSlope i) (realSlope i) := by
  apply FixedInterval.sum_mem
  intro j hj
  exact inputInverse_mem i j (others_ne hj)

def fixedCube (i : Index) : Bounds :=
  mul unitScale (mul unitScale (inputValue i) (inputValue i)) (inputValue i)
def fixedMid (i : Index) : Bounds :=
  mul unitScale (mul unitScale (constant unitScale 2) (inputValue i)) (fixedSlope i)
def subtract (I J : Bounds) : Bounds := add I (neg J)

lemma subtract_mem {I J : Bounds} {x y : ℝ} (hx : Mem unitScale I x) (hy : Mem unitScale J y) :
    Mem unitScale (subtract I J) (x-y) := by
  simpa only [subtract,sub_eq_add_neg] using mem_add hx (mem_neg hy)

lemma cube_mem (i : Index) : Mem unitScale (fixedCube i) ((value i)^3) := by
  simpa only [fixedCube,pow_succ,pow_zero,one_mul] using
    mem_mul unitScale_pos (mem_mul unitScale_pos (inputValue_mem i) (inputValue_mem i)) (inputValue_mem i)
lemma mid_mem (i : Index) : Mem unitScale (fixedMid i) (2*value i*realSlope i) := by
  exact mem_mul unitScale_pos
    (mem_mul unitScale_pos (by simpa using mem_constant unitScale 2) (inputValue_mem i)) (slope_mem i)

def realLinear (i : Index) : List ℝ :=
  [value i+2*value i*realSlope i*node i-(value i)^3*node i,
    (value i)^3-2*value i*realSlope i]

def fixedLinear (i : Index) : List Bounds :=
  [subtract (add (inputValue i) (mul unitScale (fixedMid i) (inputNode i)))
    (mul unitScale (fixedCube i) (inputNode i)), subtract (fixedCube i) (fixedMid i)]

lemma linear_mem (i : Index) : List.Forall₂ (Mem unitScale) (fixedLinear i) (realLinear i) := by
  exact List.Forall₂.cons
    (subtract_mem (mem_add (inputValue_mem i) (mem_mul unitScale_pos (mid_mem i) (inputNode_mem i)))
      (mem_mul unitScale_pos (cube_mem i) (inputNode_mem i)))
    (List.Forall₂.cons (subtract_mem (cube_mem i) (mid_mem i)) List.Forall₂.nil)

def realTerm (i : Index) : List ℝ :=
  multiply 0 (·+·) (·*·) (realLinear i)
    (multiply 0 (·+·) (·*·) (realBasis i) (realBasis i))
def fixedTerm (i : Index) : List Bounds :=
  multiply zero add (mul unitScale) (fixedLinear i)
    (multiply zero add (mul unitScale) (fixedBasis i) (fixedBasis i))

lemma term_mem (i : Index) : List.Forall₂ (Mem unitScale) (fixedTerm i) (realTerm i) :=
  mem_multiply unitScale_pos (linear_mem i) (mem_multiply unitScale_pos (basis_mem i) (basis_mem i))

lemma term_polynomial (i : Index) : polynomial (realTerm i) =
    C (value i)*HermiteInterpolation.valueBasis node i+
    C ((value i)^3)*HermiteInterpolation.derivativeBasis node i := by
  simp only [realTerm,polynomial_multiply,basis_polynomial,realLinear,polynomial]
  rw [slope_eq_derivative]
  simp [HermiteInterpolation.valueBasis,HermiteInterpolation.derivativeBasis]
  ring

def realCoefficients : List ℝ := sumCoefficients (·+·) ((List.finRange 14).map realTerm)
def fixedCoefficients : List Bounds := sumCoefficients add ((List.finRange 14).map fixedTerm)

theorem coefficients_mem : List.Forall₂ (Mem unitScale) fixedCoefficients realCoefficients := by
  unfold fixedCoefficients realCoefficients
  have h : List.Forall₂ (List.Forall₂ (Mem unitScale))
      ((List.finRange 14).map fixedTerm) ((List.finRange 14).map realTerm) :=
    rel_map (List.Forall₂ (Mem unitScale)) (List.finRange 14) fixedTerm realTerm (fun i _ => term_mem i)
  with_reducible exact (@mem_sumCoefficients unitScale
    ((List.finRange 14).map fixedTerm) ((List.finRange 14).map realTerm) h)

theorem coefficients_polynomial : polynomial realCoefficients = H := by
  rw [realCoefficients,polynomial_sumCoefficients,List.map_map]
  change ((List.finRange 14).map (fun i => polynomial (realTerm i))).sum = H
  have hn : (List.finRange 14).Nodup := by decide +kernel
  have hs := List.sum_toFinset (fun i : Index => polynomial (realTerm i)) hn
  rw [← hs]
  have heq : (List.finRange 14).toFinset = (Finset.univ : Finset Index) := by ext i; simp
  rw [heq]
  change (∑ i : Index, polynomial (realTerm i)) =
    ∑ i : Index, (C (value i)*HermiteInterpolation.valueBasis node i+
      C ((value i)^3)*HermiteInterpolation.derivativeBasis node i)
  exact Finset.sum_congr rfl (fun i _ => term_polynomial i)

theorem fixed_coefficient_mem (n : ℕ) :
    Mem unitScale ((fixedCoefficients[n]?).getD zero) (H.coeff n) := by
  have h := mem_coeff coefficients_mem n
  rw [coefficients_polynomial] at h
  exact h
end ThomsonNine.ActualHermite.Coefficients
