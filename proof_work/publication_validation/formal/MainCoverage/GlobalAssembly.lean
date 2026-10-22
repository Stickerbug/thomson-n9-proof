import MainCoverage.RootMeaning
import ThomsonNine.GramBound
import PairBounds.Energy

noncomputable section
namespace ThomsonNine.PackedMain
open scoped RealInnerProductSpace
open ThomsonNine.MainEnvelope

def gramFn (p : Fin 3 → ℝ) : ℝ := Semantics.gram (p 0) (p 1) (p 2)

theorem sum_permuted (g : ℝ → ℝ) (σ : Fin 6) (p : Fin 3 → ℝ) :
    g (permuted σ p 0)+g (permuted σ p 1)+g (permuted σ p 2)=g (p 0)+g (p 1)+g (p 2) := by
  fin_cases σ
  · rfl
  · change g (p 0)+g (p 2)+g (p 1)=_;ring
  · change g (p 1)+g (p 0)+g (p 2)=_;ring
  · change g (p 1)+g (p 2)+g (p 0)=_;ring
  · change g (p 2)+g (p 0)+g (p 1)=_;ring
  · change g (p 2)+g (p 1)+g (p 0)=_;ring

theorem residual_permuted (σ : Fin 6) (p : Fin 3 → ℝ) :
    ActualCoulombGlobal.residual (permuted σ p)=ActualCoulombGlobal.residual p := by
  have hf := F_permuted σ p
  have hc := sum_permuted ActualCoulombGlobal.coulomb σ p
  have hd := sum_permuted (fun t => ActualF.F ActualR.X 1 t t) σ p
  unfold ActualCoulombGlobal.residual
  linarith only [hf,hc,hd]

theorem gram_permuted (σ : Fin 6) (p : Fin 3 → ℝ) : gramFn (permuted σ p)=gramFn p := by
  fin_cases σ
  · rfl
  · change Semantics.gram (p 0) (p 2) (p 1)=Semantics.gram (p 0) (p 1) (p 2);unfold Semantics.gram;ring
  · change Semantics.gram (p 1) (p 0) (p 2)=Semantics.gram (p 0) (p 1) (p 2);unfold Semantics.gram;ring
  · change Semantics.gram (p 1) (p 2) (p 0)=Semantics.gram (p 0) (p 1) (p 2);unfold Semantics.gram;ring
  · change Semantics.gram (p 2) (p 0) (p 1)=Semantics.gram (p 0) (p 1) (p 2);unfold Semantics.gram;ring
  · change Semantics.gram (p 2) (p 1) (p 0)=Semantics.gram (p 0) (p 1) (p 2);unfold Semantics.gram;ring

theorem monotone_three (p : Fin 3 → ℝ) (h01 : p 0≤p 1) (h12 : p 1≤p 2) : Monotone p := by
  have h02 := h01.trans h12
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all

theorem exists_sorted_permutation (p : Fin 3 → ℝ) : ∃ σ : Fin 6, Monotone (permuted σ p) := by
  by_cases h01 : p 0≤p 1
  · by_cases h12 : p 1≤p 2
    · exact ⟨0,monotone_three _ h01 h12⟩
    · by_cases h02 : p 0≤p 2
      · exact ⟨1,monotone_three _ h02 (le_of_lt (lt_of_not_ge h12))⟩
      · exact ⟨4,monotone_three _ (le_of_lt (lt_of_not_ge h02)) h01⟩
  · by_cases h02 : p 0≤p 2
    · exact ⟨2,monotone_three _ (le_of_lt (lt_of_not_ge h01)) h02⟩
    · by_cases h12 : p 1≤p 2
      · exact ⟨3,monotone_three _ h12 (le_of_lt (lt_of_not_ge h02))⟩
      · exact ⟨5,monotone_three _ (le_of_lt (lt_of_not_ge h12)) (le_of_lt (lt_of_not_ge h01))⟩

theorem residual_nonnegative_of_ordered
    (hSorted : ∀ p, RootCube p → Monotone p → 0≤gramFn p → 0≤ActualCoulombGlobal.residual p)
    (p : Fin 3 → ℝ) (hp : RootCube p) (hg : 0≤gramFn p) : 0≤ActualCoulombGlobal.residual p := by
  obtain ⟨σ,hσ⟩ := exists_sorted_permutation p
  have hroot : RootCube (permuted σ p) := fun a => hp _
  have hGram : 0≤gramFn (permuted σ p) := by rw [gram_permuted];exact hg
  have h := hSorted (permuted σ p) hroot hσ hGram
  rw [residual_permuted] at h
  exact h

theorem frozen_claim_of_ordered_residual
    (hSorted : ∀ p, RootCube p → Monotone p → 0≤gramFn p → 0≤ActualCoulombGlobal.residual p) : ThomsonNineClaim := by
  apply ActualCoulombGlobal.frozen_claim_of_bounded_residual
  intro x hx hE i j l hij hil hjl
  let p : Fin 3 → ℝ := ![⟪x i,x j⟫,⟪x i,x l⟫,⟪x j,x l⟫]
  have hp : RootCube p := by
    intro a
    fin_cases a
    · exact ⟨(PairBounds.dot_bounds x hx i j hij).1,le_of_lt (PairBounds.pair_cutoff x hx hE i j hij)⟩
    · exact ⟨(PairBounds.dot_bounds x hx i l hil).1,le_of_lt (PairBounds.pair_cutoff x hx hE i l hil)⟩
    · exact ⟨(PairBounds.dot_bounds x hx j l hjl).1,le_of_lt (PairBounds.pair_cutoff x hx hE j l hjl)⟩
  have hg : 0≤gramFn p := gram_constraint_of_mem x hx i j l
  exact residual_nonnegative_of_ordered hSorted p hp hg
end ThomsonNine.PackedMain
