import ThomsonNine.Construction.Kernel.FeatureCache
import ThomsonNine.Construction.Kernel.QCache

-- Isolated source: Kernel.FastBasis
noncomputable section
namespace ThomsonNine.ActualKernel.FastBasis
open ThomsonNine.ContactJet
open ThomsonNine.ActualHermite.CoefficientData
open ThomsonNine.ActualKernel.BasisJet
open ThomsonNine.ActualKernel.FeatureCache
open ThomsonNine.ActualKernel.QCache

def F (p : Fin 19) (k i : Fin 11) (axis : Fin 3) : Input :=
  inputFeature (pointCode p axis) k i axis
theorem F_mem (p : Fin 19) (k i : Fin 11) (axis : Fin 3) :
    Mem unitScale (F p k i axis) (featureJet (point p) k i axis) :=
  inputFeature_mem (point p) (pointCode p axis) k i axis rfl
def pair (p : Fin 19) (k i j : Fin 11) (a b : Fin 3) : Input :=
  inputAdd (inputMul unitScale (F p k i a) (F p k j b))
    (if i=j then inputConstant FixedInterval.zero else inputMul unitScale (F p k j a) (F p k i b))
theorem pair_mem (p : Fin 19) (k i j : Fin 11) (a b : Fin 3) :
    Mem unitScale (pair p k i j a b) (pairJet (point p) k i j a b) := by
  by_cases h : i=j
  · simpa only [pair,pairJet,h,ite_true] using
      mem_add (mem_mul unitScale_pos (F_mem p k i a) (F_mem p k j b))
        (mem_constant (FixedInterval.mem_zero unitScale))
  · simpa only [pair,pairJet,h,ite_false] using
      mem_add (mem_mul unitScale_pos (F_mem p k i a) (F_mem p k j b))
        (mem_mul unitScale_pos (F_mem p k j a) (F_mem p k i b))

def raw (p : Fin 19) (σ : Fin 6) (k i j : Fin 11) : Input :=
  inputMul unitScale
    (inputMul unitScale (inputValue p σ k) (pair p k i j (permutation σ 0) (permutation σ 1)))
    (inputConstant (FixedInterval.rational unitScale (1/6)))
theorem raw_mem (p : Fin 19) (σ : Fin 6) (k i j : Fin 11) :
    Mem unitScale (raw p σ k i j) (rawJet (point p) k i j (permutation σ)) := by
  have hc : Mem unitScale (inputConstant (FixedInterval.rational unitScale (1/6))) (constant (1/6)) := by
    simpa using mem_constant (FixedInterval.rational_mem unitScale (1/6))
  exact mem_mul unitScale_pos
    (mem_mul unitScale_pos (inputValue_mem p σ k (by omega)) (pair_mem p k i j _ _)) hc

def basis (p : Fin 19) (k i j : Fin 11) : Input :=
  inputSum (List.finRange 6) (fun σ => raw p σ k i j)
theorem permutations_list : (List.finRange 6).map permutation = permutations := by decide +kernel
theorem basis_mem (p : Fin 19) (k i j : Fin 11) :
    Mem unitScale (basis p k i j) (basisJet (point p) k i j) := by
  have h := mem_sum (List.finRange 6) (fun σ => raw p σ k i j)
    (fun σ => rawJet (point p) k i j (permutation σ)) (fun σ _ => raw_mem p σ k i j)
  have he : ContactJet.sum (List.finRange 6) (fun σ => rawJet (point p) k i j (permutation σ)) =
      basisJet (point p) k i j := by
    rw [basisJet,← permutations_list]
    simp only [ContactJet.sum,List.foldr_map,Function.comp_def]
  rw [he] at h
  exact h
end ThomsonNine.ActualKernel.FastBasis
