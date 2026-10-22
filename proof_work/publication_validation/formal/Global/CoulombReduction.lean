import Global.Reduction
import PairBounds.Candidate

noncomputable section
namespace ThomsonNine.ActualCoulombGlobal
open ThomsonNine.ThreePoint ThomsonNine.ActualGlobal ThomsonNine.CertificateMatrices
open scoped BigOperators RealInnerProductSpace
def coulomb (t : ℝ) : ℝ := (Real.sqrt (2-2*t))⁻¹
def residual (x : Fin 3 → ℝ) : ℝ :=
  coulomb (x 0)+coulomb (x 1)+coulomb (x 2)-7*ActualF.F ActualR.X (x 0) (x 1) (x 2)-
    ActualF.F ActualR.X 1 (x 0) (x 0)-ActualF.F ActualR.X 1 (x 1) (x 1)-
      ActualF.F ActualR.X 1 (x 2) (x 2)-ActualF.Constants.c ActualR.X

theorem polynomial_residual_le (x : Fin 3 → ℝ) (hx : ∀ a, -1≤x a ∧ x a<1) :
    ActualR.residual x≤residual x := by
  have h0 := ActualHermite.QuotientBernstein.H_minorant (x 0) (hx 0)
  have h1 := ActualHermite.QuotientBernstein.H_minorant (x 1) (hx 1)
  have h2 := ActualHermite.QuotientBernstein.H_minorant (x 2) (hx 2)
  dsimp only [residual,ActualR.residual,coulomb]
  linarith

theorem slack_eq_residual (u v t : ℝ) :
    ((coulomb u+coulomb v+coulomb t)/3-ActualContact.E/36)-Rs scaledF 9 u v t=
      residual ![u,v,t]/3 := by
  simp only [Rs,scaledF,residual,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons,ActualF.Constants.c,ActualF.Constants.F111,diagonal_permutation]
  norm_num
  ring

theorem energy_lower_bound (x : Fin 9 → R3) (hx : x∈SphereConfig 9)
    (hR : ∀ i j l : Fin 9, i≠j → i≠l → j≠l →
      0≤residual ![⟪x i,x j⟫,⟪x i,x l⟫,⟪x j,x l⟫]) :
    familyEnergy RefinedRadius.radius≤energy x := by
  have hs12 : ∀ u v t, scaledF u v t=scaledF v u t := by
    intro u v t
    rw [scaledF,scaledF,ActualF.swap12]
  have hs23 : ∀ u v t, scaledF u v t=scaledF u t v := by
    intro u v t
    rw [scaledF,scaledF,ActualF.swap23]
  have hid := three_point_identity (n:=9) (by norm_num) scaledF hs12 hs23 coulomb ActualContact.E x hx.1
  have hmoment : 0≤∑ i, ∑ j, ∑ l, scaledF ⟪x i,x j⟫ ⟪x i,x l⟫ ⟪x j,x l⟫ := by
    simp only [scaledF,← Finset.sum_div]
    exact div_nonneg (actual_moment_nonnegative x hx.1) (by norm_num)
  have hslack : 0≤dsum (fun i j l =>
      ((coulomb ⟪x i,x j⟫+coulomb ⟪x i,x l⟫+coulomb ⟪x j,x l⟫)/3-
        ActualContact.E/(Nat.choose 9 2 : ℝ))-Rs scaledF 9 ⟪x i,x j⟫ ⟪x i,x l⟫ ⟪x j,x l⟫) := by
    apply dsum_nonneg
    intro i j l hij hil hjl
    norm_num only [Nat.choose]
    rw [slack_eq_residual]
    exact div_nonneg (hR i j l hij hil hjl) (by norm_num)
  have henergy : (∑ i : Fin 9, ∑ j∈Finset.Ioi i, coulomb ⟪x i,x j⟫)=energy x :=
    (energy_eq_inner x hx).symm
  rw [henergy,contact_energy_eq_family] at hid
  rw [contact_energy_eq_family] at hslack
  norm_num only [Nat.cast_ofNat] at hid
  nlinarith

theorem frozen_claim_of_bounded_residual
    (hR : ∀ (x : Fin 9 → R3), x∈SphereConfig 9 → energy x≤(PairBounds.U : ℝ) →
      ∀ i j l : Fin 9, i≠j → i≠l → j≠l →
        0≤residual ![⟪x i,x j⟫,⟪x i,x l⟫,⟪x j,x l⟫]) : ThomsonNineClaim := by
  apply thomsonNineClaim_of_pointwise RefinedRadius.radius RefinedRadius.radius_pos
    RefinedRadius.radius_lt_one RefinedRadius.radius_stationary
  intro x hx
  by_cases hE : energy x≤(PairBounds.U : ℝ)
  · exact energy_lower_bound x hx (hR x hx hE)
  · exact (le_of_lt PairBounds.candidate_energy_lt_U).trans (le_of_lt (lt_of_not_ge hE))
end ThomsonNine.ActualCoulombGlobal
