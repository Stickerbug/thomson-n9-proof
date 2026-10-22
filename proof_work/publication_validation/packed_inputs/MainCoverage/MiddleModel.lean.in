import MainCoverage.MiddlePerm0
import MainCoverage.MiddlePerm1
import MainCoverage.MiddlePerm2
import MainCoverage.MiddlePerm3
import MainCoverage.MiddlePerm4
import MainCoverage.MiddlePerm5
import MainCoverage.MiddleFields00
import MainCoverage.MiddleFields01
import MainCoverage.MiddleFields02
import MainCoverage.MiddleFields03
import MainCoverage.MiddleFields04
import MainCoverage.MiddleFields05
import MainCoverage.MiddleFields06
import MainCoverage.MiddleFields07
import MainCoverage.MiddleFields08
import MainCoverage.MiddleFields09
import MainCoverage.MiddleFields10
import MainCoverage.MiddleFields11
import MainCoverage.MiddleScalars

set_option maxRecDepth 100000
noncomputable section
namespace ThomsonNine.MainEnvelope.Archive
open scoped BigOperators
open ThomsonNine
theorem perm_inverse (σ : Fin 6) (j : Fin 756) : permIndex (inverse σ) (permIndex σ j)=j := by
  fin_cases σ
  · exact perm_inverse_0 j
  · exact perm_inverse_1 j
  · exact perm_inverse_2 j
  · exact perm_inverse_3 j
  · exact perm_inverse_4 j
  · exact perm_inverse_5 j
theorem perm_exponent (σ : Fin 6) (j : Fin 756) (a : Fin 3) : ActualF.Data.support (permIndex σ j) a=ActualF.Data.support j (ActualKernel.QCache.permutation σ a) := by
  fin_cases σ
  · exact perm_exponent_0 j a
  · exact perm_exponent_1 j a
  · exact perm_exponent_2 j a
  · exact perm_exponent_3 j a
  · exact perm_exponent_4 j a
  · exact perm_exponent_5 j a
theorem inverse_inverse : ∀ σ : Fin 6, inverse (inverse σ)=σ := by decide +kernel
def indexEquiv (σ : Fin 6) : Fin 756 ≃ Fin 756 where
  toFun := permIndex σ
  invFun := permIndex (inverse σ)
  left_inv := perm_inverse σ
  right_inv := by intro j;simpa only [inverse_inverse] using perm_inverse (inverse σ) j
theorem middle_fields (j : Fin 756) : symMid j=(∑ σ : Fin 6, mid (permIndex σ j))/6 ∧ kernelCoeff j=-7*symMid j-(if j=0 then cUpper+10*eps else 0) := by
  have hj := j.isLt
  by_cases h0 : j.val<64
  · exact middle_fields_0 j (by omega) h0
  by_cases h1 : j.val<128
  · exact middle_fields_1 j (by omega) h1
  by_cases h2 : j.val<192
  · exact middle_fields_2 j (by omega) h2
  by_cases h3 : j.val<256
  · exact middle_fields_3 j (by omega) h3
  by_cases h4 : j.val<320
  · exact middle_fields_4 j (by omega) h4
  by_cases h5 : j.val<384
  · exact middle_fields_5 j (by omega) h5
  by_cases h6 : j.val<448
  · exact middle_fields_6 j (by omega) h6
  by_cases h7 : j.val<512
  · exact middle_fields_7 j (by omega) h7
  by_cases h8 : j.val<576
  · exact middle_fields_8 j (by omega) h8
  by_cases h9 : j.val<640
  · exact middle_fields_9 j (by omega) h9
  by_cases h10 : j.val<704
  · exact middle_fields_10 j (by omega) h10
  exact middle_fields_11 j (by omega) (by omega)

theorem permuted_monomial (σ : Fin 6) (j : Fin 756) (x : Fin 3 → ℝ) :
    QPolynomial.monomial (ActualF.Data.support (permIndex σ j)) (permuted σ x 0) (permuted σ x 1) (permuted σ x 2)=
      QPolynomial.monomial (ActualF.Data.support j) (x 0) (x 1) (x 2) := by
  simp only [QPolynomial.monomial,perm_exponent,permuted]
  let g := fun a : Fin 3 => x a^ActualF.Data.support j a
  have hp (a : Fin 6) : g (ActualKernel.QCache.permutation a 0)*g (ActualKernel.QCache.permutation a 1)*
      g (ActualKernel.QCache.permutation a 2)=g 0*g 1*g 2 := by
    fin_cases a
    · rfl
    · change g 0*g 2*g 1=g 0*g 1*g 2;ring
    · change g 1*g 0*g 2=g 0*g 1*g 2;ring
    · change g 1*g 2*g 0=g 0*g 1*g 2;ring
    · change g 2*g 0*g 1=g 0*g 1*g 2;ring
    · change g 2*g 1*g 0=g 0*g 1*g 2;ring
  exact hp σ

theorem raw_collected (σ : Fin 6) (x : Fin 3 → ℝ) :
    middleRaw (permuted σ x)=∑ j : Fin 756, (mid (permIndex σ j) : ℝ)*
      QPolynomial.monomial (ActualF.Data.support j) (x 0) (x 1) (x 2) := by
  have hs := (indexEquiv σ).sum_comp (fun j => (mid j : ℝ)*
    QPolynomial.monomial (ActualF.Data.support j) (permuted σ x 0) (permuted σ x 1) (permuted σ x 2))
  change (∑ j : Fin 756, (mid (permIndex σ j) : ℝ)*
    QPolynomial.monomial (ActualF.Data.support (permIndex σ j))
      (permuted σ x 0) (permuted σ x 1) (permuted σ x 2))=middleRaw (permuted σ x) at hs
  rw [← hs]
  apply Finset.sum_congr rfl
  intro j hj
  exact congrArg (fun y => (mid (permIndex σ j) : ℝ)*y) (permuted_monomial σ j x)

def middlePolynomial (x : Fin 3 → ℝ) : ℝ :=
  ∑ j : Fin 756, (symMid j : ℝ)*QPolynomial.monomial (ActualF.Data.support j) (x 0) (x 1) (x 2)

theorem middle_eq_polynomial (x : Fin 3 → ℝ) : middle x=middlePolynomial x := by
  unfold middle
  simp_rw [raw_collected]
  rw [Finset.sum_comm,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.sum_mul]
  have he : (symMid j : ℝ)=(∑ σ : Fin 6, (mid (permIndex σ j) : ℝ))/6 := by exact_mod_cast (middle_fields j).1
  rw [he]
  ring

end ThomsonNine.MainEnvelope.Archive
