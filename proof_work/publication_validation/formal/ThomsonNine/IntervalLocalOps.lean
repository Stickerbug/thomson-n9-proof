import ThomsonNine.Interval

/-! Exact operations and outward-enclosure implications for saved local LDL arithmetic.

These lemmas propagate real membership through rational interval bounds. They do not
assert that a saved Hessian interval encloses the Hessian of the residual polynomial.
In particular, square uses its own sign-sensitive lower endpoint rather than treating
two occurrences of the same real variable as independent interval members.
-/

namespace ThomsonNine.Interval.RatInterval

/-- Widen an enclosure using exact rational endpoint comparisons. -/
theorem mem_subset {I K : RatInterval} {x : ℝ} (hx : I.mem x)
    (hlo : K.lo ≤ I.lo) (hhi : I.hi ≤ K.hi) : K.mem x := by
  exact ⟨le_trans (by exact_mod_cast hlo) hx.1,
    le_trans hx.2 (by exact_mod_cast hhi)⟩

private theorem scalar_mul_bounds {a b x t L U : ℝ}
    (hxlo : a ≤ x) (hxhi : x ≤ b)
    (hLa : L ≤ a * t) (hLb : L ≤ b * t)
    (haU : a * t ≤ U) (hbU : b * t ≤ U) :
    L ≤ x * t ∧ x * t ≤ U := by
  rcases le_total 0 t with ht | ht
  · exact ⟨le_trans hLa (mul_le_mul_of_nonneg_right hxlo ht),
      le_trans (mul_le_mul_of_nonneg_right hxhi ht) hbU⟩
  · exact ⟨le_trans hLb (mul_le_mul_of_nonpos_right hxhi ht),
      le_trans (mul_le_mul_of_nonpos_right hxlo ht) haU⟩

/-- Any rational interval containing all four corner products encloses the product.
The four lower comparisons are followed by the four upper comparisons. -/
theorem mem_mul_of_bounds {I J K : RatInterval} {x y : ℝ}
    (hx : I.mem x) (hy : J.mem y)
    (hll : K.lo ≤ I.lo * J.lo) (hlh : K.lo ≤ I.lo * J.hi)
    (hhl : K.lo ≤ I.hi * J.lo) (hhh : K.lo ≤ I.hi * J.hi)
    (ull : I.lo * J.lo ≤ K.hi) (ulh : I.lo * J.hi ≤ K.hi)
    (uhl : I.hi * J.lo ≤ K.hi) (uhh : I.hi * J.hi ≤ K.hi) :
    K.mem (x * y) := by
  have hlow : (K.lo : ℝ) ≤ x * (J.lo : ℝ) ∧
      x * (J.lo : ℝ) ≤ (K.hi : ℝ) :=
    scalar_mul_bounds hx.1 hx.2 (by exact_mod_cast hll)
      (by exact_mod_cast hhl) (by exact_mod_cast ull) (by exact_mod_cast uhl)
  have hhigh : (K.lo : ℝ) ≤ x * (J.hi : ℝ) ∧
      x * (J.hi : ℝ) ≤ (K.hi : ℝ) :=
    scalar_mul_bounds hx.1 hx.2 (by exact_mod_cast hlh)
      (by exact_mod_cast hhh) (by exact_mod_cast ulh) (by exact_mod_cast uhh)
  rcases le_total 0 x with hx0 | hx0
  · exact ⟨le_trans hlow.1 (mul_le_mul_of_nonneg_left hy.1 hx0),
      le_trans (mul_le_mul_of_nonneg_left hy.2 hx0) hhigh.2⟩
  · exact ⟨le_trans hhigh.1 (mul_le_mul_of_nonpos_left hy.2 hx0),
      le_trans (mul_le_mul_of_nonpos_left hy.1 hx0) hlow.2⟩

/-- Exact four-corner interval product, before any fixed-point outward rounding. -/
def mul (I J : RatInterval) : RatInterval :=
  ⟨min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)),
   max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi)),
   le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
     (le_trans (le_max_left _ _) (le_max_left _ _)))⟩

theorem mem_mul {I J : RatInterval} {x y : ℝ} (hx : I.mem x) (hy : J.mem y) :
    (mul I J).mem (x * y) := by
  apply mem_mul_of_bounds hx hy <;> simp [mul, min_le_iff, le_max_iff]

/-- Bounds for a square, with the three sign cases of its input interval explicit.
The first lower premise applies to nonnegative intervals, the second to nonpositive
intervals, and the third to intervals containing zero. The upper endpoint contains
both endpoint squares. Premises on a zero endpoint may overlap harmlessly. -/
theorem mem_square_of_bounds {I K : RatInterval} {x : ℝ} (hx : I.mem x)
    (hpos : 0 ≤ I.lo → K.lo ≤ I.lo ^ 2)
    (hneg : I.hi ≤ 0 → K.lo ≤ I.hi ^ 2)
    (hcross : I.lo ≤ 0 → 0 ≤ I.hi → K.lo ≤ 0)
    (ulo : I.lo ^ 2 ≤ K.hi) (uhi : I.hi ^ 2 ≤ K.hi) :
    K.mem (x ^ 2) := by
  constructor
  · by_cases hI : 0 ≤ I.lo
    · have hlo : (0 : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast hI
      have hs := pow_le_pow_left₀ hlo hx.1 2
      have hb : (K.lo : ℝ) ≤ (I.lo : ℝ) ^ 2 := by exact_mod_cast hpos hI
      exact le_trans hb hs
    · by_cases hJ : I.hi ≤ 0
      · have hhi : (I.hi : ℝ) ≤ 0 := by exact_mod_cast hJ
        have hs := pow_le_pow_left₀ (neg_nonneg.mpr hhi) (neg_le_neg hx.2) 2
        have hb : (K.lo : ℝ) ≤ (I.hi : ℝ) ^ 2 := by exact_mod_cast hneg hJ
        have hs' : (I.hi : ℝ) ^ 2 ≤ x ^ 2 := by simpa only [neg_sq] using hs
        exact le_trans hb hs'
      · have hb : K.lo ≤ 0 := hcross (le_of_lt (not_le.mp hI))
          (le_of_lt (not_le.mp hJ))
        exact le_trans (by exact_mod_cast hb) (sq_nonneg x)
  · rcases le_total 0 x with hx0 | hx0
    · have hs := pow_le_pow_left₀ hx0 hx.2 2
      exact le_trans hs (by exact_mod_cast uhi)
    · have hs := pow_le_pow_left₀ (neg_nonneg.mpr hx0) (neg_le_neg hx.1) 2
      have hs' : x ^ 2 ≤ (I.lo : ℝ) ^ 2 := by simpa only [neg_sq] using hs
      exact le_trans hs' (by exact_mod_cast ulo)

/-- Exact square enclosure: its lower endpoint is zero when the input straddles zero. -/
def square (I : RatInterval) : RatInterval :=
  ⟨if 0 ≤ I.lo then I.lo ^ 2 else if I.hi ≤ 0 then I.hi ^ 2 else 0,
   max (I.lo ^ 2) (I.hi ^ 2), by
    by_cases h0 : 0 ≤ I.lo
    · simp only [if_pos h0]
      exact le_max_left _ _
    · by_cases h1 : I.hi ≤ 0
      · simp only [if_neg h0, if_pos h1]
        exact le_max_right _ _
      · simp only [if_neg h0, if_neg h1]
        exact le_trans (sq_nonneg _) (le_max_left _ _)⟩

theorem mem_square {I : RatInterval} {x : ℝ} (hx : I.mem x) :
    (square I).mem (x ^ 2) := by
  apply mem_square_of_bounds hx
  · intro h
    simp [square, h]
  · intro h
    by_cases h0 : 0 ≤ I.lo
    · have hz : I.lo = 0 := le_antisymm (le_trans I.h h) h0
      have hz' : I.hi = 0 := le_antisymm h (le_trans h0 I.h)
      simp [square, h0, hz, hz']
    · simp [square, h0, h]
  · intro hlo hhi
    by_cases h0 : 0 ≤ I.lo
    · have hz : I.lo = 0 := le_antisymm hlo h0
      simp [square, h0, hz]
    · by_cases h1 : I.hi ≤ 0
      · have hz : I.hi = 0 := le_antisymm h1 hhi
        simp [square, h0, h1, hz]
      · simp [square, h0, h1]
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- Exact reciprocal of an interval with strictly positive lower endpoint. -/
def reciprocalPos (J : RatInterval) (hJ : 0 < J.lo) : RatInterval :=
  ⟨1 / J.hi, 1 / J.lo, one_div_le_one_div_of_le hJ J.h⟩

theorem mem_reciprocalPos {J : RatInterval} (hJ : 0 < J.lo) {y : ℝ}
    (hy : J.mem y) : (reciprocalPos J hJ).mem (1 / y) := by
  have hlo : (0 : ℝ) < (J.lo : ℝ) := by exact_mod_cast hJ
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le hlo hy.1
  constructor
  · change ((1 / J.hi : ℚ) : ℝ) ≤ 1 / y
    push_cast
    exact one_div_le_one_div_of_le hy0 hy.2
  · change 1 / y ≤ ((1 / J.lo : ℚ) : ℝ)
    push_cast
    exact one_div_le_one_div_of_le hlo hy.1

/-- Exact division by a positive interval. -/
def divPos (I J : RatInterval) (hJ : 0 < J.lo) : RatInterval :=
  mul I (reciprocalPos J hJ)

theorem mem_divPos {I J : RatInterval} (hJ : 0 < J.lo) {x y : ℝ}
    (hx : I.mem x) (hy : J.mem y) : (divPos I J hJ).mem (x / y) := by
  simpa only [divPos, div_eq_mul_inv, one_div, one_mul] using
    mem_mul hx (mem_reciprocalPos hJ hy)

/-- Saved rounded division endpoints may be justified by four exact corner quotients.
Strict positivity excludes every denominator pole; numerators may have either sign. -/
theorem mem_div_pos_of_bounds {I J K : RatInterval} {x y : ℝ}
    (hJ : 0 < J.lo) (hx : I.mem x) (hy : J.mem y)
    (hll : K.lo ≤ I.lo / J.lo) (hlh : K.lo ≤ I.lo / J.hi)
    (hhl : K.lo ≤ I.hi / J.lo) (hhh : K.lo ≤ I.hi / J.hi)
    (ull : I.lo / J.lo ≤ K.hi) (ulh : I.lo / J.hi ≤ K.hi)
    (uhl : I.hi / J.lo ≤ K.hi) (uhh : I.hi / J.hi ≤ K.hi) :
    K.mem (x / y) := by
  have hm : K.mem (x * (1 / y)) := by
    apply mem_mul_of_bounds hx (mem_reciprocalPos hJ hy)
    · simpa only [reciprocalPos, div_eq_mul_inv, one_div, one_mul] using hlh
    · simpa only [reciprocalPos, div_eq_mul_inv, one_div, one_mul] using hll
    · simpa only [reciprocalPos, div_eq_mul_inv, one_div, one_mul] using hhh
    · simpa only [reciprocalPos, div_eq_mul_inv, one_div, one_mul] using hhl
    · simpa only [reciprocalPos, div_eq_mul_inv, one_div, one_mul] using ulh
    · simpa only [reciprocalPos, div_eq_mul_inv, one_div, one_mul] using ull
    · simpa only [reciprocalPos, div_eq_mul_inv, one_div, one_mul] using uhh
    · simpa only [reciprocalPos, div_eq_mul_inv, one_div, one_mul] using uhl
  simpa only [div_eq_mul_inv, one_div, one_mul] using hm

end ThomsonNine.Interval.RatInterval
