import MainCoverage.MiddleModel

noncomputable section
namespace ThomsonNine.MainEnvelope.Archive
open scoped BigOperators
open ThomsonNine

def kernelPolynomial (x : Fin 3 → ℝ) : ℝ :=
  ∑ j : Fin 756, (kernelCoeff j : ℝ)*QPolynomial.monomial (ActualF.Data.support j) (x 0) (x 1) (x 2)

theorem kernel_polynomial_eq (x : Fin 3 → ℝ) :
    kernelPolynomial x= -7*middle x-(cUpper : ℝ)-10*(epsilon : ℝ) := by
  have hK (j : Fin 756) : (kernelCoeff j : ℝ)= -7*(symMid j : ℝ)-
      (if j=0 then (cUpper : ℝ)+10*(eps : ℝ) else 0) := by
    have he := congrArg (fun q : ℚ => (q : ℝ)) (middle_fields j).2
    by_cases hj : j=0
    · simp only [if_pos hj] at he ⊢
      push_cast at he
      norm_num only [] at he
      exact he
    · simp only [if_neg hj] at he ⊢
      push_cast at he
      norm_num only [] at he
      simpa only [sub_zero] using he
  have hA : (∑ j : Fin 756, (-7*(symMid j : ℝ))*
      QPolynomial.monomial (ActualF.Data.support j) (x 0) (x 1) (x 2))= -7*middlePolynomial x := by
    rw [middlePolynomial,Finset.mul_sum]
    apply Finset.sum_congr rfl;intro j hj;ring
  unfold kernelPolynomial
  simp_rw [hK,sub_mul]
  rw [Finset.sum_sub_distrib,hA]
  have hB : (∑ j : Fin 756, (if j=0 then (cUpper : ℝ)+10*(eps : ℝ) else 0)*
      QPolynomial.monomial (ActualF.Data.support j) (x 0) (x 1) (x 2))=(cUpper : ℝ)+10*(eps : ℝ) := by
    simp [ite_mul,support_zero,QPolynomial.monomial]
  rw [hB,← middle_eq_polynomial,← epsilon_fields]
  ring

theorem archive_residual_lower (x : Fin 3 → ℝ) (hx : ∀ a, |x a|≤1) :
    kernelPolynomial x+(ActualCoulombGlobal.coulomb (x 0)-diagonal (x 0))+
      (ActualCoulombGlobal.coulomb (x 1)-diagonal (x 1))+
      (ActualCoulombGlobal.coulomb (x 2)-diagonal (x 2))≤ActualCoulombGlobal.residual x := by
  have hC : (ActualF.Constants.cInterval.hi : ℝ)≤(cUpper : ℝ) := by exact_mod_cast c_upper_valid
  have hk : kernelPolynomial x≤kernel x := by
    rw [kernel_polynomial_eq]
    dsimp only [kernel]
    linarith
  have hh := residual_lower x hx
  linarith
end ThomsonNine.MainEnvelope.Archive
