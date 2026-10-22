import MainCoverage.RootSourceModel
import MainCoverage.RootTensor.K01Proof
import MainCoverage.RootTensor.K02Proof
import MainCoverage.RootTensor.K03Proof
import MainCoverage.RootTensor.GProof
import MainCoverage.SourceRelation1
import MainCoverage.SourceRelation2
import MainCoverage.SourceRelation3
import MainCoverage.GramSourceFields
import MainCoverage.TreeSound

set_option maxRecDepth 100000
noncomputable section
namespace ThomsonNine.PackedMain
open ThomsonNine.PackedTensor

def penalizedKernel (q : Fin 4) (x : Fin 3 → ℝ) : ℝ :=
  MainEnvelope.Archive.kernelPolynomial x-(penalty q : ℝ)*Semantics.gram (x 0) (x 1) (x 2)

theorem source_polynomial_relation (b1 b0 : CubeIndex 11 → ℤ) (d1 d0 : ℕ) (lam : ℝ)
    (h : ∀ p, (b1 p : ℝ)/(d1 : ℝ)=(b0 p : ℝ)/(d0 : ℝ)+lam*(gramInput 11 p : ℝ))
    (x : Fin 3 → ℝ) :
    tri (scaledInt b1 d1) (fun i => (x 0)^i.val) (fun j => (x 1)^j.val) (fun k => (x 2)^k.val)=
      tri (scaledInt b0 d0) (fun i => (x 0)^i.val) (fun j => (x 1)^j.val) (fun k => (x 2)^k.val)-
        lam*Semantics.gram (x 0) (x 1) (x 2) := by
  have he : scaledInt b1 d1=fun p => scaledInt b0 d0 p+lam*(gramInput 11 p : ℝ) := funext h
  rw [he,tri_add,tri_scale,gramInput_polynomial11]
  ring

theorem source_meaning0 (x : Fin 3 → ℝ) : RootTensor.K00.sourcePolynomial x=penalizedKernel 0 x := by
  have hz : penalty 0=0 := by decide +kernel
  rw [penalizedKernel,hz,Rat.cast_zero,zero_mul,sub_zero]
  exact RootSource.source_eq_kernel x

theorem source_meaning1 (x : Fin 3 → ℝ) : RootTensor.K01.sourcePolynomial x=penalizedKernel 1 x := by
  have hr (p : CubeIndex 11) : (RootTensor.K01.coeff0 p : ℝ)/(RootTensor.K01.denominator0 : ℝ)=
      (RootTensor.K00.coeff0 p : ℝ)/(RootTensor.K00.denominator0 : ℝ)+(penalty 1 : ℝ)*(gramInput 11 p : ℝ) := by
    exact_mod_cast source_relation_1 p.1 p.2.1 p.2.2
  have hh := source_polynomial_relation _ _ _ _ _ hr x
  change RootTensor.K01.sourcePolynomial x=RootTensor.K00.sourcePolynomial x-(penalty 1 : ℝ)*Semantics.gram (x 0) (x 1) (x 2) at hh
  rw [RootSource.source_eq_kernel] at hh
  exact hh

theorem source_meaning2 (x : Fin 3 → ℝ) : RootTensor.K02.sourcePolynomial x=penalizedKernel 2 x := by
  have hr (p : CubeIndex 11) : (RootTensor.K02.coeff0 p : ℝ)/(RootTensor.K02.denominator0 : ℝ)=
      (RootTensor.K00.coeff0 p : ℝ)/(RootTensor.K00.denominator0 : ℝ)+(penalty 2 : ℝ)*(gramInput 11 p : ℝ) := by
    exact_mod_cast source_relation_2 p.1 p.2.1 p.2.2
  have hh := source_polynomial_relation _ _ _ _ _ hr x
  change RootTensor.K02.sourcePolynomial x=RootTensor.K00.sourcePolynomial x-(penalty 2 : ℝ)*Semantics.gram (x 0) (x 1) (x 2) at hh
  rw [RootSource.source_eq_kernel] at hh
  exact hh

theorem source_meaning3 (x : Fin 3 → ℝ) : RootTensor.K03.sourcePolynomial x=penalizedKernel 3 x := by
  have hr (p : CubeIndex 11) : (RootTensor.K03.coeff0 p : ℝ)/(RootTensor.K03.denominator0 : ℝ)=
      (RootTensor.K00.coeff0 p : ℝ)/(RootTensor.K00.denominator0 : ℝ)+(penalty 3 : ℝ)*(gramInput 11 p : ℝ) := by
    exact_mod_cast source_relation_3 p.1 p.2.1 p.2.2
  have hh := source_polynomial_relation _ _ _ _ _ hr x
  change RootTensor.K03.sourcePolynomial x=RootTensor.K00.sourcePolynomial x-(penalty 3 : ℝ)*Semantics.gram (x 0) (x 1) (x 2) at hh
  rw [RootSource.source_eq_kernel] at hh
  exact hh

theorem gram_source_meaning (x : Fin 3 → ℝ) : RootTensor.G.sourcePolynomial x= -Semantics.gram (x 0) (x 1) (x 2) := by
  have hc : scaledInt RootTensor.G.coeff0 RootTensor.G.denominator0=fun p => (gramInput 3 p : ℝ) := by
    funext p
    change (RootTensor.G.coeff0 p : ℝ)/(RootTensor.G.denominator0 : ℝ)=(gramInput 3 p : ℝ)
    exact_mod_cast gram_source_fields p.1 p.2.1 p.2.2
  unfold RootTensor.G.sourcePolynomial
  rw [hc,gramInput_polynomial3]

theorem actual_root_frame : Frame penalizedKernel (fun x => Semantics.gram (x 0) (x 1) (x 2)) rootState := by
  constructor
  · intro q z hz
    fin_cases q
    · exact (RootTensor.K00.root_lower z hz).trans_eq (source_meaning0 _)
    · exact (RootTensor.K01.root_lower z hz).trans_eq (source_meaning1 _)
    · exact (RootTensor.K02.root_lower z hz).trans_eq (source_meaning2 _)
    · exact (RootTensor.K03.root_lower z hz).trans_eq (source_meaning3 _)
  · intro z hz
    exact (RootTensor.G.root_lower z hz).trans_eq (gram_source_meaning _)

theorem actual_dominates : Dominates penalizedKernel (fun x => Semantics.gram (x 0) (x 1) (x 2))
    ActualCoulombGlobal.residual (fun t => ActualCoulombGlobal.coulomb t-MainEnvelope.diagonal t) := by
  intro q x hx hG
  have hAbs (a : Fin 3) : |x a|≤1 := abs_le.mpr ⟨(hx a).1,((hx a).2.trans (by norm_num : (14:ℝ)/25≤1))⟩
  have hR := MainEnvelope.Archive.archive_residual_lower x hAbs
  have hl : (0:ℝ)≤(penalty q : ℝ) := by exact_mod_cast penalty_nonnegative q
  have hp := mul_nonneg hl hG
  dsimp only [penalizedKernel]
  linarith

theorem actual_fallback : Fallback penalizedKernel (fun x => Semantics.gram (x 0) (x 1) (x 2)) :=
  fallback_of_root_frame _ _ rootState (fun _ => rfl) (fun _ => rfl) actual_root_frame

theorem root_valid : valid rootState := by intro a;norm_num [rootState]
end ThomsonNine.PackedMain
