import ThomsonNine.Construction.Global.Moment
import ThomsonNine.Construction.R.Residual
import ThomsonNine.ActualHermiteMinorant
import ThomsonNine.FinalAssembly
import ThomsonNine.Applications

-- Isolated source: Global.Reduction
noncomputable section
namespace ThomsonNine.ActualGlobal
open ThomsonNine.ThreePoint ThomsonNine.CertificateMatrices
open scoped BigOperators RealInnerProductSpace

def scaledF (u v t : ℝ) : ℝ := ActualF.F ActualR.X u v t/3

theorem diagonal_permutation (X : Fin 190 → ℝ) (u : ℝ) : ActualF.F X u u 1=ActualF.F X 1 u u := by
  rw [ActualF.swap23 X u u 1,ActualF.swap12 X u 1 u]

theorem slack_eq_residual (u v t : ℝ) :
    ((ActualHermite.H.eval u+ActualHermite.H.eval v+ActualHermite.H.eval t)/3-
      ActualContact.E/36)-Rs scaledF 9 u v t=ActualR.residual ![u,v,t]/3 := by
  simp only [Rs,scaledF,ActualR.residual,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,ActualF.Constants.c,ActualF.Constants.F111,diagonal_permutation]
  norm_num
  ring

theorem hermite_pair_lower_bound (x : Fin 9 → R3) (hx : x∈SphereConfig 9)
    (hR : ∀ i j l : Fin 9, i≠j → i≠l → j≠l →
      0≤ActualR.residual ![⟪x i,x j⟫,⟪x i,x l⟫,⟪x j,x l⟫]) :
    ActualContact.E≤∑ i, ∑ j∈Finset.Ioi i, ActualHermite.H.eval ⟪x i,x j⟫ := by
  have hs12 : ∀ u v t, scaledF u v t=scaledF v u t := by
    intro u v t
    rw [scaledF,scaledF,ActualF.swap12]
  have hs23 : ∀ u v t, scaledF u v t=scaledF u t v := by
    intro u v t
    rw [scaledF,scaledF,ActualF.swap23]
  have hid := three_point_identity (n:=9) (by norm_num) scaledF hs12 hs23
    (fun t => ActualHermite.H.eval t) ActualContact.E x hx.1
  have hmoment : 0≤∑ i, ∑ j, ∑ l, scaledF ⟪x i,x j⟫ ⟪x i,x l⟫ ⟪x j,x l⟫ := by
    simp only [scaledF,← Finset.sum_div]
    exact div_nonneg (actual_moment_nonnegative x hx.1) (by norm_num)
  have hslack : 0≤dsum (fun i j l =>
      ((ActualHermite.H.eval ⟪x i,x j⟫+ActualHermite.H.eval ⟪x i,x l⟫+
        ActualHermite.H.eval ⟪x j,x l⟫)/3-ActualContact.E/(Nat.choose 9 2 : ℝ))-
        Rs scaledF 9 ⟪x i,x j⟫ ⟪x i,x l⟫ ⟪x j,x l⟫) := by
    apply dsum_nonneg
    intro i j l hij hil hjl
    norm_num only [Nat.choose] 
    rw [slack_eq_residual]
    exact div_nonneg (hR i j l hij hil hjl) (by norm_num)
  norm_num only [Nat.cast_ofNat] at hid
  nlinarith
theorem hermite_sum_le_energy (x : Fin 9 → R3) (hx : x∈SphereConfig 9) :
    (∑ i, ∑ j∈Finset.Ioi i, ActualHermite.H.eval ⟪x i,x j⟫)≤energy x := by
  rw [energy_eq_inner x hx]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  have hij : i≠j := ne_of_lt (Finset.mem_Ioi.mp hj)
  have hd : 0<‖x i-x j‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hx.2.ne hij))
  have he := norm_sub_sq_eq_inner x hx i j
  have hupper : ⟪x i,x j⟫<1 := by nlinarith [sq_pos_of_pos hd]
  have ha := abs_real_inner_le_norm (x i) (x j)
  rw [hx.1 i,hx.1 j,one_mul] at ha
  exact ActualHermite.QuotientBernstein.H_minorant _ ⟨(abs_le.mp ha).1,hupper⟩

theorem energy_lower_bound (x : Fin 9 → R3) (hx : x∈SphereConfig 9)
    (hR : ∀ i j l : Fin 9, i≠j → i≠l → j≠l →
      0≤ActualR.residual ![⟪x i,x j⟫,⟪x i,x l⟫,⟪x j,x l⟫]) :
    familyEnergy RefinedRadius.radius≤energy x := by
  have h := hermite_pair_lower_bound x hx hR
  rw [contact_energy_eq_family] at h
  exact h.trans (hermite_sum_le_energy x hx)

/-- This is an assembly implication. Its residual hypothesis still needs the local/coverage proof. -/
theorem frozen_claim_of_residual_on_triples
    (hR : ∀ (x : Fin 9 → R3), x∈SphereConfig 9 →
      ∀ i j l : Fin 9, i≠j → i≠l → j≠l →
        0≤ActualR.residual ![⟪x i,x j⟫,⟪x i,x l⟫,⟪x j,x l⟫]) : ThomsonNineClaim := by
  apply thomsonNineClaim_of_pointwise RefinedRadius.radius RefinedRadius.radius_pos
    RefinedRadius.radius_lt_one RefinedRadius.radius_stationary
  intro x hx
  exact energy_lower_bound x hx (hR x hx)
/-- The numerical pair reduction is needed only below a candidate upper bound. -/
theorem frozen_claim_of_bounded_residual (U : ℝ)
    (hU : familyEnergy RefinedRadius.radius≤U)
    (hR : ∀ (x : Fin 9 → R3), x∈SphereConfig 9 → energy x≤U →
      ∀ i j l : Fin 9, i≠j → i≠l → j≠l →
        0≤ActualR.residual ![⟪x i,x j⟫,⟪x i,x l⟫,⟪x j,x l⟫]) : ThomsonNineClaim := by
  apply thomsonNineClaim_of_pointwise RefinedRadius.radius RefinedRadius.radius_pos
    RefinedRadius.radius_lt_one RefinedRadius.radius_stationary
  intro x hx
  by_cases he : energy x≤U
  · exact energy_lower_bound x hx (hR x hx he)
  · exact hU.trans (le_of_lt (lt_of_not_ge he))
end ThomsonNine.ActualGlobal
