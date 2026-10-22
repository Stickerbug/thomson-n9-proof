import PairAddition.Identity

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.PairAddition
open Polynomial ThomsonNine.ThreePoint
open scoped BigOperators RealInnerProductSpace

theorem feature_lengths : ∀ f, (features f).coefficients.length≤38 := by decide +kernel

theorem quad_Y3_eq (k : ℕ) (w : Fin 38 → ℝ) (u v t : ℝ) :
    w ⬝ᵥ (Y3 38 k u v t).mulVec w=
      (∑ i : Fin 38, w i*u^i.val)*(∑ j : Fin 38, w j*v^j.val)*Q3 k u v t := by
  simp only [dotProduct,Matrix.mulVec,Y3,Matrix.of_apply,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  ring

def featureMoment (f : Fin 138) (x : Fin 9 → R3) : ℝ :=
  ∑ j : Fin 9, ∑ l : Fin 9,
    phi f ⟪x 0,x j⟫*phi f ⟪x 0,x l⟫*Q3 (features f).order.val ⟪x 0,x j⟫ ⟪x 0,x l⟫ ⟪x j,x l⟫

theorem featureMoment_nonnegative (f : Fin 138) (x : Fin 9 → R3) (hx : ∀ i, ‖x i‖=1) :
    0≤featureMoment f x := by
  let w : Fin 38 → ℝ := fun i => (((features f).coefficients[i.val]?).getD 0 : ℤ)
  have hw (u : ℝ) : (∑ i : Fin 38, w i*u^i.val)=phi f u :=
    (IntegerListPolynomial.eval_fin_sum 38 (features f).coefficients (feature_lengths f) u).symm
  obtain ⟨a,b,hfr⟩ := exists_tangent_frame (x 0) (hx 0)
  have h := quad_Y3_nonneg 38 (features f).order.val (fun j => ⟪x 0,x j⟫)
    (fun j l => ⟪x j,x l⟫) (fun j => ⟪a,x j⟫) (fun j => ⟪b,x j⟫)
    (fun j => (hfr (x j) (x j) (hx j) (hx j)).1)
    (fun j l => (hfr (x j) (x l) (hx j) (hx l)).2) w
  simpa only [featureMoment,quad_Y3_eq,hw] using h

theorem moment_identity (x : Fin 9 → R3) :
    (∑ j : Fin 9, ∑ l : Fin 9, P.eval ⟪x j,x l⟫)=
      ∑ f : Fin 138, ((features f).weight : ℝ)*featureMoment f x := by
  calc
    (∑ j : Fin 9, ∑ l : Fin 9, P.eval ⟪x j,x l⟫)=
        ∑ j : Fin 9, ∑ l : Fin 9, ∑ f : Fin 138,
          ((features f).weight : ℝ)*phi f ⟪x 0,x j⟫*phi f ⟪x 0,x l⟫*
            Q3 (features f).order.val ⟪x 0,x j⟫ ⟪x 0,x l⟫ ⟪x j,x l⟫ := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro l hl
      exact addition_identity _ _ _
    _ = ∑ f : Fin 138, ((features f).weight : ℝ)*featureMoment f x := by
      simp_rw [Finset.sum_comm (s:=(Finset.univ : Finset (Fin 9))) (t:=(Finset.univ : Finset (Fin 138)))]
      simp only [featureMoment,Finset.mul_sum,mul_assoc]

theorem moment_lower_bound (x : Fin 9 → R3) (hx : ∀ i, ‖x i‖=1) :
    81*((features 0).weight : ℝ)≤∑ j : Fin 9, ∑ l : Fin 9, P.eval ⟪x j,x l⟫ := by
  have hnon (f : Fin 138) : 0≤((features f).weight : ℝ)*featureMoment f x :=
    mul_nonneg (by exact_mod_cast le_of_lt (weights_positive f)) (featureMoment_nonnegative f x hx)
  have h := Finset.single_le_sum (fun f _ => hnon f) (Finset.mem_univ (0 : Fin 138))
  rw [← moment_identity] at h
  have hz : featureMoment 0 x=81 := by
    norm_num [featureMoment,phi,features,Q3,IntegerListPolynomial.realPolynomial,ListPolynomial.polynomial]
  rw [hz] at h
  linarith
end ThomsonNine.PairAddition
