import PairBounds.Leaf00
import PairBounds.Leaf01
import PairBounds.Leaf02
import PairBounds.Leaf03
import PairBounds.Leaf04
import PairBounds.Leaf05
import PairBounds.Leaf06
import PairBounds.Leaf07
import PairBounds.Leaf08
import PairBounds.Leaf09
import PairBounds.Leaf10
import PairBounds.Leaf11
import PairBounds.Leaf12
import PairBounds.StrictMinorant
set_option maxRecDepth 100000
noncomputable section
namespace ThomsonNine.PairBounds
open Polynomial ThomsonNine.RationalListPolynomial
theorem g_nonnegative (x : ℝ) (hx : -1≤x ∧ x≤1) : 0≤(realPolynomial gList).eval x := by
  by_cases h0 : x≤(-7/8 : ℝ)
  · have h := Leaf00.value_lower x (by norm_num [Leaf00.lo,Leaf00.hi];constructor <;> linarith)
    simpa [Leaf00.lower] using h
  by_cases h1 : x≤(-3/4 : ℝ)
  · have h := Leaf01.value_lower x (by norm_num [Leaf01.lo,Leaf01.hi];constructor <;> linarith)
    simpa [Leaf01.lower] using h
  by_cases h2 : x≤(-1/2 : ℝ)
  · have h := Leaf02.value_lower x (by norm_num [Leaf02.lo,Leaf02.hi];constructor <;> linarith)
    simpa [Leaf02.lower] using h
  by_cases h3 : x≤(-3/8 : ℝ)
  · have h := Leaf03.value_lower x (by norm_num [Leaf03.lo,Leaf03.hi];constructor <;> linarith)
    simpa [Leaf03.lower] using h
  by_cases h4 : x≤(-1/4 : ℝ)
  · have h := Leaf04.value_lower x (by norm_num [Leaf04.lo,Leaf04.hi];constructor <;> linarith)
    simpa [Leaf04.lower] using h
  by_cases h5 : x≤(0/1 : ℝ)
  · have h := Leaf05.value_lower x (by norm_num [Leaf05.lo,Leaf05.hi];constructor <;> linarith)
    simpa [Leaf05.lower] using h
  by_cases h6 : x≤(1/4 : ℝ)
  · have h := Leaf06.value_lower x (by norm_num [Leaf06.lo,Leaf06.hi];constructor <;> linarith)
    simpa [Leaf06.lower] using h
  by_cases h7 : x≤(9/32 : ℝ)
  · have h := Leaf07.value_lower x (by norm_num [Leaf07.lo,Leaf07.hi];constructor <;> linarith)
    simpa [Leaf07.lower] using h
  by_cases h8 : x≤(5/16 : ℝ)
  · have h := Leaf08.value_lower x (by norm_num [Leaf08.lo,Leaf08.hi];constructor <;> linarith)
    simpa [Leaf08.lower] using h
  by_cases h9 : x≤(3/8 : ℝ)
  · have h := Leaf09.value_lower x (by norm_num [Leaf09.lo,Leaf09.hi];constructor <;> linarith)
    simpa [Leaf09.lower] using h
  by_cases h10 : x≤(1/2 : ℝ)
  · have h := Leaf10.value_lower x (by norm_num [Leaf10.lo,Leaf10.hi];constructor <;> linarith)
    simpa [Leaf10.lower] using h
  have h := Leaf11.value_lower x (by norm_num [Leaf11.lo,Leaf11.hi];constructor <;> linarith)
  simpa [Leaf11.lower] using h
theorem coulomb_minorant (x : ℝ) (hx : -1≤x) (ht : x<1) :
    PairAddition.P.eval x≤(Real.sqrt (2-2*x))⁻¹ := by
  apply HermiteFactor.minorant_of_G_nonneg PairAddition.P x ht
  rw [← g_polynomial]
  exact g_nonnegative x ⟨hx,le_of_lt ht⟩
theorem gGap_positive (x : ℝ) (hx : (14/25 : ℝ)≤x ∧ x≤1) :
    0<(realPolynomial gGapList).eval x := by
  have h := Leaf12.value_lower x (by norm_num [Leaf12.lo,Leaf12.hi];exact hx)
  have hp : (0 : ℝ)<Leaf12.lower := by
    exact_mod_cast (show 0<Leaf12.lower from by decide +kernel)
  exact hp.trans_le h
theorem exclusion_strict (x : ℝ) (hx : (14/25 : ℝ)≤x) (ht : x<1) :
    PairAddition.P.eval x+(gap : ℝ)<(Real.sqrt (2-2*x))⁻¹ := by
  have hG : 0<(HermiteFactor.G (PairAddition.P+C (gap : ℝ))).eval x := by
    rw [← gGap_polynomial]
    exact gGap_positive x ⟨hx,le_of_lt ht⟩
  simpa only [eval_add,eval_C] using HermiteFactor.strict_minorant_of_G_positive
    (PairAddition.P+C (gap : ℝ)) x ht hG
theorem gap_positive : 0<gap := by decide +kernel
theorem U_eq_B_add_gap : U=B+gap := by decide +kernel
end ThomsonNine.PairBounds
