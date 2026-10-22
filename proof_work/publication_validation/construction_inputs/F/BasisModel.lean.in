import ThomsonNine.Construction.F.ReducedExpansion
import ThomsonNine.Construction.F.BasisData
import ThomsonNine.Construction.Algebra.FiniteCollector

-- Isolated source: F.BasisModel
noncomputable section
namespace ThomsonNine.ActualF
open ThomsonNine.CertificateMatrices ThomsonNine.ActualKernel.BasisJet
open ThomsonNine.ContactJet ThomsonNine.MonomialSymmetry
open scoped BigOperators

def single (k i j : Fin 11) (y : Point) : ℝ :=
  (permutations.map (fun σ => ThreePoint.Q3 k (y (σ 0)) (y (σ 1)) (y (σ 2))*
    feature k i (y (σ 0))*feature k j (y (σ 1))*(1/6))).sum

theorem basis_eq_single (k i j : Fin 11) (y : Point) :
    basisFunction k i j y=single k i j y+if i=j then 0 else single k j i y := by
  by_cases h : i=j
  · simp only [basisFunction,single,permutations,rawFunction,pairFeature,h,ite_true,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    ring
  · simp only [basisFunction,single,permutations,rawFunction,pairFeature,h,ite_false,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    ring

theorem matrix_pairing_eq_sum_single (X : Fin 190 → ℝ) (k : Fin 11) (u v t : ℝ) :
    ThreePoint.matDot (A X k) (ThreePoint.S3 (ambientDim k) k u v t)=
      ∑ i : Fin (reducedDim k), ∑ j : Fin (reducedDim k),
        reduced X k i j*single k (reducedIndex k i) (reducedIndex k j) ![u,v,t] := by
  rw [matDot_S3]
  simp only [reducedEntry,single,permutations,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  simp only [Finset.sum_mul,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

def sourceValue (X : Fin 190 → ℝ) (y : Point) (s : BasisData.Triple) : ℝ :=
  X (indices s.1 s.2.1 s.2.2)*single s.1 s.2.1 s.2.2 y

theorem basis_allSources_sum (X : Fin 190 → ℝ) (u v t : ℝ) :
    (BasisData.allSources.map (sourceValue X ![u,v,t])).sum=F X u v t := by
  rw [F_eq_matrix_pairing,BasisData.allSources,flatMap_sum_map,finRange_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [flatMap_sum_map,finRange_sum,matrix_pairing_eq_sum_single]
  apply Finset.sum_congr rfl
  intro i hi
  rw [List.map_map,finRange_sum]
  rfl

theorem group_sum (X : Fin 190 → ℝ) (y : Point) (h : Fin 190) :
    ((BasisData.group h).map (sourceValue X y)).sum=
      X h*basisFunction (ActualContact.indices h).block (ActualContact.indices h).left (ActualContact.indices h).right y := by
  rw [BasisData.group,List.map_append,List.sum_append]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,sourceValue,
    BasisData.left_index,BasisData.right_index]
  rw [basis_eq_single]
  have hr : sourceValue X y (BasisData.right h)=X h*single (ActualContact.indices h).block
      (ActualContact.indices h).right (ActualContact.indices h).left y := by
    rw [sourceValue,BasisData.right_index]
    rfl
  by_cases he : (ActualContact.indices h).left=(ActualContact.indices h).right
  · simp [BasisData.offDiagonal,he,BasisData.left,hr]
  · simp [BasisData.offDiagonal,he,BasisData.left,hr,mul_add]

theorem F_eq_contact_basis (X : Fin 190 → ℝ) (u v t : ℝ) :
    F X u v t=∑ h : Fin 190, X h*
      basisFunction (ActualContact.indices h).block (ActualContact.indices h).left (ActualContact.indices h).right ![u,v,t] := by
  have hp := List.Perm.sum_eq (BasisData.partition.map (sourceValue X ![u,v,t]))
  rw [basis_allSources_sum] at hp
  rw [← hp,BasisData.gathered,flatMap_sum_map,finRange_sum]
  exact Finset.sum_congr rfl (fun h _ => group_sum X ![u,v,t] h)
end ThomsonNine.ActualF
