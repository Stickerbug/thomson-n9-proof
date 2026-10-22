import PairBounds.BernsteinModel
import Algebra.ExactComposition

noncomputable section
namespace ThomsonNine.PairBounds
open Polynomial ThomsonNine.RationalListPolynomial

theorem leaf_lower (source localPoly : List ℚ) (lo hi lower : ℚ) (b : Fin 76 → ℚ)
    (hwidth : lo<hi) (hcompose : ExactPolynomial.compose source [lo,hi-lo]=localPoly)
    (hbern : PairBernstein75.combination b=localPoly) (hb : ∀ i, lower≤b i)
    (x : ℝ) (hx : (lo : ℝ)≤x ∧ x≤(hi : ℝ)) :
    (lower : ℝ)≤(realPolynomial source).eval x := by
  let s := (x-(lo : ℝ))/((hi-lo : ℚ) : ℝ)
  have hw : (0 : ℝ)<((hi-lo : ℚ) : ℝ) := by exact_mod_cast sub_pos.mpr hwidth
  have hs : 0≤s ∧ s≤1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hx.1) (le_of_lt hw)
    · apply (div_le_one hw).mpr
      push_cast
      linarith [hx.2]
  have h := PairBernstein75.combination_lower b (lower : ℝ) s hs (fun i => by exact_mod_cast hb i)
  have he : realPolynomial (PairBernstein75.combination b)=
      (realPolynomial source).comp (realPolynomial [lo,hi-lo]) := by
    rw [hbern,← hcompose,ExactPolynomial.compose_sound]
  rw [he,eval_comp] at h
  have harg : (realPolynomial [lo,hi-lo]).eval s=x := by
    simp only [RationalListPolynomial.cons,RationalListPolynomial.nil,mul_zero,add_zero,
      eval_add,eval_C,eval_mul,eval_X]
    dsimp only [s]
    field_simp
    ring
  rw [harg] at h
  exact h
end ThomsonNine.PairBounds
