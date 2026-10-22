import PairBounds.Minorant
import PairAddition.Positivity
import ThomsonNine.Applications
import ThomsonNine.ThreePointBound

set_option maxRecDepth 100000
noncomputable section
namespace ThomsonNine.PairBounds
open Polynomial
open scoped BigOperators RealInnerProductSpace
def pOne : ℚ := ∑ i : Fin 38, PairAddition.pCoefficient i
def polynomialSum (x : Fin 9 → R3) : ℝ :=
  ∑ i : Fin 9, ∑ j∈Finset.Ioi i, PairAddition.P.eval ⟪x i,x j⟫
def pairError (x : Fin 9 → R3) (i j : Fin 9) : ℝ :=
  (Real.sqrt (2-2*⟪x i,x j⟫))⁻¹-PairAddition.P.eval ⟪x i,x j⟫

theorem P_one : PairAddition.P.eval 1=(pOne : ℝ) := by
  rw [PairAddition.P,PairAddition.eval_ofFn]
  simp only [one_pow,mul_one]
  exact_mod_cast (show (∑ i : Fin 38, PairAddition.pCoefficient i)=pOne from rfl)
theorem B_formula : 81*(PairAddition.features 0).weight-9*pOne=2*B := by decide +kernel

theorem moment_pair_identity (x : Fin 9 → R3) (hx : ∀ i, ‖x i‖=1) :
    (∑ i : Fin 9, ∑ j : Fin 9, PairAddition.P.eval ⟪x i,x j⟫)=9*(pOne : ℝ)+2*polynomialSum x := by
  let f : Fin 9 → Fin 9 → ℝ := fun i j => PairAddition.P.eval ⟪x i,x j⟫
  have hs : ∀ i j, f i j=f j i := fun i j => congrArg PairAddition.P.eval (real_inner_comm _ _)
  have he : (∑ i : Fin 9, ∑ j : Fin 9, f i j)=
      (∑ i : Fin 9, ∑ j : Fin 9, if i=j then f i j else 0)+
      (∑ i : Fin 9, ∑ j : Fin 9, if i≠j then f i j else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i=j <;> simp [hij]
  have hd : (∑ i : Fin 9, ∑ j : Fin 9, if i=j then f i j else 0)=∑ i : Fin 9, f i i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp
  have hii (i : Fin 9) : f i i=PairAddition.P.eval 1 := by
    dsimp only [f]
    rw [real_inner_self_eq_norm_sq,hx i]
    norm_num
  rw [hd,ThreePoint.sum_ne_eq_two_sum_Ioi f hs] at he
  simpa only [hii,P_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,f,polynomialSum,Nat.cast_ofNat] using he

theorem B_le_polynomialSum (x : Fin 9 → R3) (hx : ∀ i, ‖x i‖=1) : (B : ℝ)≤polynomialSum x := by
  have h := PairAddition.moment_lower_bound x hx
  rw [moment_pair_identity x hx] at h
  have hb : 81*((PairAddition.features 0).weight : ℝ)-9*(pOne : ℝ)=2*(B : ℝ) := by exact_mod_cast B_formula
  linarith

theorem dot_bounds (x : Fin 9 → R3) (hx : x∈SphereConfig 9) (i j : Fin 9) (hij : i≠j) :
    -1≤⟪x i,x j⟫ ∧ ⟪x i,x j⟫<1 := by
  have ha := abs_real_inner_le_norm (x i) (x j)
  rw [hx.1 i,hx.1 j,one_mul] at ha
  have hd : 0<‖x i-x j‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hx.2.ne hij))
  have hs := norm_sub_sq_eq_inner x hx i j
  exact ⟨(abs_le.mp ha).1,by nlinarith [sq_pos_of_pos hd]⟩

theorem pairError_nonnegative (x : Fin 9 → R3) (hx : x∈SphereConfig 9) (i j : Fin 9) (hij : i≠j) :
    0≤pairError x i j := by
  have hd := dot_bounds x hx i j hij
  exact sub_nonneg.mpr (coulomb_minorant _ hd.1 hd.2)

theorem sum_errors (x : Fin 9 → R3) (hx : x∈SphereConfig 9) :
    (∑ i : Fin 9, ∑ j∈Finset.Ioi i, pairError x i j)=energy x-polynomialSum x := by
  simp only [pairError,Finset.sum_sub_distrib,polynomialSum]
  rw [energy_eq_inner x hx]

theorem energy_gt_U_of_close_pair (x : Fin 9 → R3) (hx : x∈SphereConfig 9)
    (i j : Fin 9) (hij : i<j) (hclose : (14/25 : ℝ)≤⟪x i,x j⟫) : (U : ℝ)<energy x := by
  have he (a b : Fin 9) (hab : b∈Finset.Ioi a) : 0≤pairError x a b :=
    pairError_nonnegative x hx a b (ne_of_lt (Finset.mem_Ioi.mp hab))
  have hrow (a : Fin 9) : 0≤∑ b∈Finset.Ioi a, pairError x a b :=
    Finset.sum_nonneg (fun b hb => he a b hb)
  have hi := Finset.single_le_sum (fun b hb => he i b hb) (Finset.mem_Ioi.mpr hij)
  have ht := Finset.single_le_sum (fun a _ => hrow a) (Finset.mem_univ i)
  have hchosen := hi.trans ht
  have hstrict := exclusion_strict _ hclose (dot_bounds x hx i j (ne_of_lt hij)).2
  have hgap : (gap : ℝ)<pairError x i j := by dsimp only [pairError];linarith
  have hB := B_le_polynomialSum x hx.1
  have hsum := sum_errors x hx
  have hU : (U : ℝ)=(B : ℝ)+(gap : ℝ) := by exact_mod_cast U_eq_B_add_gap
  linarith

theorem pair_cutoff (x : Fin 9 → R3) (hx : x∈SphereConfig 9) (hE : energy x≤(U : ℝ))
    (i j : Fin 9) (hij : i≠j) : ⟪x i,x j⟫<(14/25 : ℝ) := by
  by_contra h
  have hclose : (14/25 : ℝ)≤⟪x i,x j⟫ := le_of_not_gt h
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact (not_lt_of_ge hE) (energy_gt_U_of_close_pair x hx i j hlt hclose)
  · have hc : (14/25 : ℝ)≤⟪x j,x i⟫ := by simpa only [real_inner_comm] using hclose
    exact (not_lt_of_ge hE) (energy_gt_U_of_close_pair x hx j i hgt hc)
end ThomsonNine.PairBounds
