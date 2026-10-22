import MainCoverage.RootSourceFields
import MainCoverage.RootTensor.K00Proof
import MainCoverage.KernelEnvelope
import Algebra.MonomialSymmetry

set_option maxRecDepth 100000
noncomputable section
namespace ThomsonNine.PackedMain.RootSource
open scoped BigOperators
open ThomsonNine.PackedTensor

def inputCoeff (id : ℕ) : ℝ := (RootTensor.K00.coeff0 (unflat 11 id) : ℝ)/(RootTensor.K00.denominator0 : ℝ)
def inputMonomial (x : Fin 3 → ℝ) (id : ℕ) : ℝ :=
  (x 0)^(coord 0 (unflat 11 id)).val*(x 1)^(coord 1 (unflat 11 id)).val*(x 2)^(coord 2 (unflat 11 id)).val
def targetMonomial (x : Fin 3 → ℝ) (j : Fin 757) : ℝ :=
  if h : j.val<756 then QPolynomial.monomial (ActualF.Data.support ⟨j.val,h⟩) (x 0) (x 1) (x 2) else 1

theorem zero_coefficient (id : ℕ) (hi : id∈zeroIndices) : inputCoeff id=0 := by
  have hb := (List.all_eq_true.mp zero_fields) id hi
  have he := of_decide_eq_true hb
  simp only [inputCoeff,he,Int.cast_zero,zero_div]

theorem grouped_coefficient (j : Fin 756) :
    ((groups j.castSucc).map inputCoeff).sum=(MainEnvelope.Archive.kernelCoeff j : ℝ) := by
  have hg : groups j.castSucc=[sourceIndex j] := by simp [groups,j.isLt]
  rw [hg]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  unfold inputCoeff
  exact_mod_cast (all_source_fields j).1

theorem grouped_last : ((groups (Fin.last 756)).map inputCoeff).sum=0 := by
  have hg : groups (Fin.last 756)=zeroIndices := by simp [groups]
  rw [hg]
  apply List.sum_eq_zero
  intro v hv
  obtain ⟨id,hi,rfl⟩ := List.mem_map.mp hv
  exact zero_coefficient id hi

def indexEquiv : Fin 1331 ≃ CubeIndex 11 where
  toFun i := unflat 11 i.val
  invFun p := ⟨flat p,flat_lt p⟩
  left_inv i := Fin.ext (flat_unflat i)
  right_inv := unflat_flat

theorem raw_sum_eq_source (x : Fin 3 → ℝ) :
    ((List.range 1331).map (fun i => inputCoeff i*inputMonomial x i)).sum=RootTensor.K00.sourcePolynomial x := by
  let f := fun p : CubeIndex 11 => ((RootTensor.K00.coeff0 p : ℝ)/(RootTensor.K00.denominator0 : ℝ))*
    ((x 0)^(coord 0 p).val*(x 1)^(coord 1 p).val*(x 2)^(coord 2 p).val)
  have he := indexEquiv.sum_comp f
  change (∑ i : Fin 1331, inputCoeff i.val*inputMonomial x i.val)=(∑ p : CubeIndex 11, f p) at he
  rw [FiniteCollector.range_sum_eq_fin,he]
  simp only [Fintype.sum_prod_type]
  unfold RootTensor.K00.sourcePolynomial tri
  apply Finset.sum_congr rfl;intro i hi
  apply Finset.sum_congr rfl;intro j hj
  apply Finset.sum_congr rfl;intro k hk
  change ((RootTensor.K00.coeff0 (i,j,k) : ℝ)/(RootTensor.K00.denominator0 : ℝ))*
    ((x 0)^i.val*(x 1)^j.val*(x 2)^k.val)=
      ((RootTensor.K00.coeff0 (i,j,k) : ℝ)/(RootTensor.K00.denominator0 : ℝ))*(x 0)^i.val*(x 1)^j.val*(x 2)^k.val
  ring

theorem source_eq_kernel (x : Fin 3 → ℝ) : RootTensor.K00.sourcePolynomial x=MainEnvelope.Archive.kernelPolynomial x := by
  have hm : ∀ j∈List.finRange 757, ∀ i∈groups j, inputCoeff i=0 ∨ inputMonomial x i=targetMonomial x j := by
    intro j hj i hi
    by_cases hlt : j.val<756
    · have hg : groups j=[sourceIndex ⟨j.val,hlt⟩] := dif_pos hlt
      rw [hg] at hi
      have he : i=sourceIndex ⟨j.val,hlt⟩ := List.mem_singleton.mp hi
      subst i
      right
      have hE := (all_source_fields ⟨j.val,hlt⟩).2
      simp only [inputMonomial,targetMonomial,dif_pos hlt,QPolynomial.monomial]
      rw [hE 0,hE 1,hE 2]
    · have hg : groups j=zeroIndices := dif_neg hlt
      rw [hg] at hi
      exact Or.inl (zero_coefficient i hi)
  have hp := FiniteCollector.partition_of_fuel_sorted sorted_groups
  have hh := FiniteCollector.collected_eval_zero (List.finRange 757) groups 1331 inputCoeff
    (inputMonomial x) (targetMonomial x) hp hm
  rw [MonomialSymmetry.finRange_sum,Fin.sum_univ_castSucc] at hh
  have hT (j : Fin 756) : targetMonomial x j.castSucc=
      QPolynomial.monomial (ActualF.Data.support j) (x 0) (x 1) (x 2) := by simp [targetMonomial,j.isLt]
  simp_rw [grouped_coefficient,hT] at hh
  rw [grouped_last,zero_mul,add_zero,raw_sum_eq_source] at hh
  exact hh.symm
end ThomsonNine.PackedMain.RootSource
