import Kernel.FeatureCacheData
noncomputable section
namespace ThomsonNine.ActualKernel.FeatureCache
open ThomsonNine.ContactJet
open ThomsonNine.ActualHermite.CoefficientData
open ThomsonNine.ActualKernel.BasisJet
open ThomsonNine.ListPolynomial
theorem cached_value_mem (n : Fin 7) (k i : Fin 11) :
    FixedInterval.Mem unitScale (cachedValue n k i) ((polynomial (coefficients k i)).eval (coordinateValue n)) := by
  have h := (feature_mem (canonical_mem n) k i 0).1
  have hf := fields n k i
  have he : (featureJet (canonicalPoint n) k i 0).value=(polynomial (coefficients k i)).eval (coordinateValue n) := by
    rw [featureJet,horner_value]
    rfl
  rw [← he]
  change ((cachedValue n k i).lo : ℝ)≤(unitScale : ℝ)*(featureJet (canonicalPoint n) k i 0).value ∧
    (unitScale : ℝ)*(featureJet (canonicalPoint n) k i 0).value≤(cachedValue n k i).hi
  rw [← hf.1,← hf.2.1]
  exact h
theorem cached_derivative_mem (n : Fin 7) (k i : Fin 11) :
    FixedInterval.Mem unitScale (cachedDerivative n k i) ((polynomial (coefficients k i)).derivative.eval (coordinateValue n)) := by
  have h := (feature_mem (canonical_mem n) k i 0).2 0
  have hf := fields n k i
  have he : (featureJet (canonicalPoint n) k i 0).gradient 0 =
      (polynomial (coefficients k i)).derivative.eval (coordinateValue n) := by
    simp [featureJet,horner_gradient,coordinate,canonicalPoint]
  rw [he] at h
  change ((cachedDerivative n k i).lo : ℝ)≤(unitScale : ℝ)*(polynomial (coefficients k i)).derivative.eval (coordinateValue n) ∧
    (unitScale : ℝ)*(polynomial (coefficients k i)).derivative.eval (coordinateValue n)≤(cachedDerivative n k i).hi
  rw [← hf.2.2.1,← hf.2.2.2]
  exact h
def inputFeature (n : Fin 7) (k i : Fin 11) (axis : Fin 3) : Input :=
  ⟨cachedValue n k i,fun j => if axis=j then cachedDerivative n k i else FixedInterval.zero⟩
theorem inputFeature_mem (x : Point) (n : Fin 7) (k i : Fin 11) (axis : Fin 3)
    (hx : x axis=coordinateValue n) : Mem unitScale (inputFeature n k i axis) (featureJet x k i axis) := by
  constructor
  · change FixedInterval.Mem unitScale (cachedValue n k i) ((horner (coordinate x axis) (coefficients k i)).value)
    rw [horner_value]
    change FixedInterval.Mem unitScale (cachedValue n k i) ((polynomial (coefficients k i)).eval (x axis))
    rw [hx]
    exact cached_value_mem n k i
  · intro j
    change FixedInterval.Mem unitScale (if axis=j then cachedDerivative n k i else FixedInterval.zero)
      ((horner (coordinate x axis) (coefficients k i)).gradient j)
    rw [horner_gradient]
    by_cases h : axis=j
    · subst j
      simpa [coordinate,hx] using cached_derivative_mem n k i
    · simpa [coordinate,h] using FixedInterval.mem_zero unitScale
end ThomsonNine.ActualKernel.FeatureCache
