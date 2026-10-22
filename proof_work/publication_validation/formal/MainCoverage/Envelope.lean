import F.Bounds
import F.Symmetry
import F.Constants
import Global.CoulombReduction

set_option maxRecDepth 100000
noncomputable section
namespace ThomsonNine.MainEnvelope
open scoped BigOperators
open ThomsonNine

def mid (j : Fin 756) : ℚ := ((ActualF.Data.coefficientInterval j).lo+(ActualF.Data.coefficientInterval j).hi)/2
def error (j : Fin 756) : ℚ := ((ActualF.Data.coefficientInterval j).hi-(ActualF.Data.coefficientInterval j).lo)/2
def epsilon : ℚ := ∑ j, error j
def middleRaw (x : Fin 3 → ℝ) : ℝ :=
  ∑ j, (mid j : ℝ)*QPolynomial.monomial (ActualF.Data.support j) (x 0) (x 1) (x 2)
def permuted (σ : Fin 6) (x : Fin 3 → ℝ) : Fin 3 → ℝ := fun a => x (ActualKernel.QCache.permutation σ a)
def middle (x : Fin 3 → ℝ) : ℝ := (∑ σ : Fin 6, middleRaw (permuted σ x))/6

theorem actual_mid_error (j : Fin 756) : |ActualF.coefficient ActualR.X j-(mid j : ℝ)|≤(error j : ℝ) := by
  have h := ActualF.Certified.actual_coefficient_mem j
  change ((ActualF.Data.coefficientInterval j).lo : ℝ)≤_ ∧ _≤((ActualF.Data.coefficientInterval j).hi : ℝ) at h
  rw [abs_le]
  simp only [mid,error,Rat.cast_div,Rat.cast_add,Rat.cast_sub,Rat.cast_ofNat]
  constructor <;> linarith

theorem monomial_bound (e : QPolynomial.Exponent) (x : Fin 3 → ℝ) (hx : ∀ a, |x a|≤1) :
    |QPolynomial.monomial e (x 0) (x 1) (x 2)|≤1 := by
  simp only [QPolynomial.monomial,abs_mul,abs_pow]
  have h0 := pow_le_one₀ (abs_nonneg (x 0)) (hx 0) (n:=e 0)
  have h1 := pow_le_one₀ (abs_nonneg (x 1)) (hx 1) (n:=e 1)
  have h2 := pow_le_one₀ (abs_nonneg (x 2)) (hx 2) (n:=e 2)
  calc
    |x 0|^(e 0)*|x 1|^(e 1)*|x 2|^(e 2)≤(1*1)*(1 : ℝ) :=
      mul_le_mul (mul_le_mul h0 h1 (pow_nonneg (abs_nonneg _) _) (by norm_num)) h2
        (pow_nonneg (abs_nonneg _) _) (by norm_num)
    _ = 1 := by norm_num

theorem raw_error (x : Fin 3 → ℝ) (hx : ∀ a, |x a|≤1) :
    |ActualF.F ActualR.X (x 0) (x 1) (x 2)-middleRaw x|≤(epsilon : ℝ) := by
  have he : ActualF.F ActualR.X (x 0) (x 1) (x 2)-middleRaw x=
      ∑ j : Fin 756, (ActualF.coefficient ActualR.X j-(mid j : ℝ))*
        QPolynomial.monomial (ActualF.Data.support j) (x 0) (x 1) (x 2) := by
    simp only [ActualF.F,middleRaw,sub_mul,Finset.sum_sub_distrib]
  rw [he]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ j : Fin 756, |(ActualF.coefficient ActualR.X j-(mid j : ℝ))*
        QPolynomial.monomial (ActualF.Data.support j) (x 0) (x 1) (x 2)|)≤∑ j : Fin 756, (error j : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (monomial_bound _ x hx) (abs_nonneg _)).trans
        (by simpa only [mul_one] using actual_mid_error j)
    _ = (epsilon : ℝ) := by simp [epsilon]

theorem F_permuted (σ : Fin 6) (x : Fin 3 → ℝ) :
    ActualF.F ActualR.X (permuted σ x 0) (permuted σ x 1) (permuted σ x 2)=
      ActualF.F ActualR.X (x 0) (x 1) (x 2) := by
  fin_cases σ
  · rfl
  · exact ActualF.swap23 _ _ _ _
  · exact ActualF.swap12 _ _ _ _
  · exact (ActualF.swap23 ActualR.X (x 1) (x 2) (x 0)).trans (ActualF.swap12 _ _ _ _)
  · exact (ActualF.swap12 ActualR.X (x 2) (x 0) (x 1)).trans (ActualF.swap23 _ _ _ _)
  · exact (ActualF.swap12 ActualR.X (x 2) (x 1) (x 0)).trans
      ((ActualF.swap23 ActualR.X (x 1) (x 2) (x 0)).trans (ActualF.swap12 _ _ _ _))

theorem F_upper (x : Fin 3 → ℝ) (hx : ∀ a, |x a|≤1) :
    ActualF.F ActualR.X (x 0) (x 1) (x 2)≤middle x+(epsilon : ℝ) := by
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun (σ : Fin 6) _ =>
    (abs_le.mp (raw_error (permuted σ x) (fun a => hx _))).2)
  simp only [F_permuted] at hs
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  norm_num only [Nat.cast_ofNat] at hs
  dsimp only [middle]
  linarith

def diagonal (t : ℝ) : ℝ := middle ![1,t,t]
def kernel (x : Fin 3 → ℝ) : ℝ :=
  -7*middle x-(ActualF.Constants.cInterval.hi : ℝ)-10*(epsilon : ℝ)

theorem residual_lower (x : Fin 3 → ℝ) (hx : ∀ a, |x a|≤1) :
    kernel x+(ActualCoulombGlobal.coulomb (x 0)-diagonal (x 0))+
      (ActualCoulombGlobal.coulomb (x 1)-diagonal (x 1))+
      (ActualCoulombGlobal.coulomb (x 2)-diagonal (x 2))≤ActualCoulombGlobal.residual x := by
  have hf := F_upper x hx
  have hd (a : Fin 3) := F_upper (![1,x a,x a]) (by intro i;fin_cases i <;> simp [hx])
  have hc := ActualF.Constants.actual_c_mem.2
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons] at hd
  dsimp only [kernel,diagonal,ActualCoulombGlobal.residual]
  have h0 := hd 0;have h1 := hd 1;have h2 := hd 2
  nlinarith
end ThomsonNine.MainEnvelope
