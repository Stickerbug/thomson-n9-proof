import ThomsonNine.Construction.Kernel.Data
import ThomsonNine.Construction.Algebra.JetPolynomial

-- Isolated source: Kernel.BasisJet
noncomputable section
namespace ThomsonNine.ActualKernel.BasisJet
open ThomsonNine.ContactJet
open ThomsonNine.ListPolynomial
open ThomsonNine.ActualHermite.CoefficientData

def coefficients (k i : Fin 11) : List ℝ := (List.finRange 11).map (N k i)
def inputCoefficients (k i : Fin 11) : List FixedInterval.Bounds := (List.finRange 11).map (cachedN k i)
theorem coefficients_mem (k i : Fin 11) :
    List.Forall₂ (FixedInterval.Mem unitScale) (inputCoefficients k i) (coefficients k i) :=
  rel_map _ _ _ _ (fun j _ => cachedN_mem k i j)
def feature (k i : Fin 11) (u : ℝ) : ℝ := (polynomial (coefficients k i)).eval u
def featureJet (x : Point) (k i : Fin 11) (axis : Fin 3) : Jet := horner (coordinate x axis) (coefficients k i)
def inputFeatureJet (x : Fin 3 → FixedInterval.Bounds) (k i : Fin 11) (axis : Fin 3) : Input :=
  inputHorner unitScale (inputCoordinate unitScale x axis) (inputCoefficients k i)
theorem feature_correct (x : Point) (k i : Fin 11) (axis : Fin 3) :
    Correct (fun y => feature k i (y axis)) x (featureJet x k i axis) :=
  correct_horner (correct_coordinate x axis) (coefficients k i)
theorem feature_mem {x : Point} {I : Fin 3 → FixedInterval.Bounds}
    (hx : ∀ i, FixedInterval.Mem unitScale (I i) (x i)) (k i : Fin 11) (axis : Fin 3) :
    Mem unitScale (inputFeatureJet I k i axis) (featureJet x k i axis) :=
  mem_horner unitScale_pos (mem_coordinate hx axis) (coefficients_mem k i)

def permutations : List (Fin 3 → Fin 3) :=
  [![0,1,2],![0,2,1],![1,0,2],![1,2,0],![2,0,1],![2,1,0]]
def pairFeature (k i j : Fin 11) (u v : ℝ) : ℝ :=
  feature k i u*feature k j v+if i=j then 0 else feature k j u*feature k i v
def pairJet (x : Point) (k i j : Fin 11) (a b : Fin 3) : Jet :=
  add (mul (featureJet x k i a) (featureJet x k j b))
    (if i=j then constant 0 else mul (featureJet x k j a) (featureJet x k i b))
def inputPairJet (x : Fin 3 → FixedInterval.Bounds) (k i j : Fin 11) (a b : Fin 3) : Input :=
  inputAdd (inputMul unitScale (inputFeatureJet x k i a) (inputFeatureJet x k j b))
    (if i=j then inputConstant FixedInterval.zero else inputMul unitScale (inputFeatureJet x k j a) (inputFeatureJet x k i b))
theorem pair_correct (x : Point) (k i j : Fin 11) (a b : Fin 3) :
    Correct (fun y => pairFeature k i j (y a) (y b)) x (pairJet x k i j a b) := by
  by_cases h : i=j
  · simpa only [pairFeature,pairJet,h,ite_true] using
      ((feature_correct x k i a).mul (feature_correct x k j b)).add (correct_constant 0 x)
  · simpa only [pairFeature,pairJet,h,ite_false] using
      ((feature_correct x k i a).mul (feature_correct x k j b)).add
        ((feature_correct x k j a).mul (feature_correct x k i b))
theorem pair_mem {x : Point} {I : Fin 3 → FixedInterval.Bounds}
    (hx : ∀ i, FixedInterval.Mem unitScale (I i) (x i)) (k i j : Fin 11) (a b : Fin 3) :
    Mem unitScale (inputPairJet I k i j a b) (pairJet x k i j a b) := by
  by_cases h : i=j
  · simpa only [inputPairJet,pairJet,h,ite_true] using
      mem_add (mem_mul unitScale_pos (feature_mem hx k i a) (feature_mem hx k j b))
        (mem_constant (FixedInterval.mem_zero unitScale))
  · simpa only [inputPairJet,pairJet,h,ite_false] using
      mem_add (mem_mul unitScale_pos (feature_mem hx k i a) (feature_mem hx k j b))
        (mem_mul unitScale_pos (feature_mem hx k j a) (feature_mem hx k i b))

def rawFunction (k i j : Fin 11) (σ : Fin 3 → Fin 3) (y : Point) : ℝ :=
  ThreePoint.Q3 k (y (σ 0)) (y (σ 1)) (y (σ 2))*pairFeature k i j (y (σ 0)) (y (σ 1))*(1/6)
def rawJet (x : Point) (k i j : Fin 11) (σ : Fin 3 → Fin 3) : Jet :=
  mul (mul (q (coordinate x (σ 0)) (coordinate x (σ 1)) (coordinate x (σ 2)) k)
    (pairJet x k i j (σ 0) (σ 1))) (constant (1/6))
def inputRawJet (x : Fin 3 → FixedInterval.Bounds) (k i j : Fin 11) (σ : Fin 3 → Fin 3) : Input :=
  inputMul unitScale (inputMul unitScale
    (inputQ unitScale (inputCoordinate unitScale x (σ 0)) (inputCoordinate unitScale x (σ 1)) (inputCoordinate unitScale x (σ 2)) k)
    (inputPairJet x k i j (σ 0) (σ 1))) (inputConstant (FixedInterval.rational unitScale (1/6)))
theorem raw_correct (x : Point) (k i j : Fin 11) (σ : Fin 3 → Fin 3) :
    Correct (rawFunction k i j σ) x (rawJet x k i j σ) :=
  ((correct_q (correct_coordinate x (σ 0)) (correct_coordinate x (σ 1)) (correct_coordinate x (σ 2)) k).mul
    (pair_correct x k i j (σ 0) (σ 1))).mul (correct_constant (1/6) x)
theorem raw_mem {x : Point} {I : Fin 3 → FixedInterval.Bounds}
    (hx : ∀ i, FixedInterval.Mem unitScale (I i) (x i)) (k i j : Fin 11) (σ : Fin 3 → Fin 3) :
    Mem unitScale (inputRawJet I k i j σ) (rawJet x k i j σ) := by
  have hc : Mem unitScale (inputConstant (FixedInterval.rational unitScale (1/6))) (constant (1/6)) := by
    simpa using mem_constant (FixedInterval.rational_mem unitScale (1/6))
  exact mem_mul unitScale_pos (mem_mul unitScale_pos
    (mem_q unitScale_pos (mem_coordinate hx (σ 0)) (mem_coordinate hx (σ 1)) (mem_coordinate hx (σ 2)) k)
    (pair_mem hx k i j (σ 0) (σ 1))) hc

def basisFunction (k i j : Fin 11) (y : Point) : ℝ := (permutations.map (fun σ => rawFunction k i j σ y)).sum
def basisJet (x : Point) (k i j : Fin 11) : Jet := ContactJet.sum permutations (rawJet x k i j)
def inputBasisJet (x : Fin 3 → FixedInterval.Bounds) (k i j : Fin 11) : Input := inputSum permutations (inputRawJet x k i j)
theorem basis_correct (x : Point) (k i j : Fin 11) : Correct (basisFunction k i j) x (basisJet x k i j) :=
  correct_sum permutations (rawFunction k i j) (rawJet x k i j) x (fun σ _ => raw_correct x k i j σ)
theorem basis_mem {x : Point} {I : Fin 3 → FixedInterval.Bounds}
    (hx : ∀ i, FixedInterval.Mem unitScale (I i) (x i)) (k i j : Fin 11) :
    Mem unitScale (inputBasisJet I k i j) (basisJet x k i j) :=
  mem_sum permutations (inputRawJet I k i j) (rawJet x k i j) (fun σ _ => raw_mem hx k i j σ)
end ThomsonNine.ActualKernel.BasisJet
