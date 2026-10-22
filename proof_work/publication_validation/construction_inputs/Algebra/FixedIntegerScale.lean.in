import ThomsonNine.FixedIntervalSigned

-- Isolated source: Algebra.FixedIntegerScale
noncomputable section
namespace ThomsonNine.FixedInterval
def scaleInteger (n : ℤ) (I : Bounds) : Bounds :=
  if 0≤n then ⟨n*I.lo,n*I.hi⟩ else ⟨n*I.hi,n*I.lo⟩
theorem mem_scaleInteger {s : ℤ} (n : ℤ) {I : Bounds} {x : ℝ} (hx : Mem s I x) :
    Mem s (scaleInteger n I) ((n : ℝ)*x) := by
  by_cases hn : 0≤n
  · have hn' : (0 : ℝ)≤n := by exact_mod_cast hn
    simp only [scaleInteger,if_pos hn]
    constructor
    · change ((n*I.lo : ℤ) : ℝ)≤(s : ℝ)*((n : ℝ)*x)
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hx.1 hn']
    · change (s : ℝ)*((n : ℝ)*x)≤((n*I.hi : ℤ) : ℝ)
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hx.2 hn']
  · have hn' : (n : ℝ)≤0 := by exact_mod_cast le_of_lt (lt_of_not_ge hn)
    simp only [scaleInteger,if_neg hn]
    constructor
    · change ((n*I.hi : ℤ) : ℝ)≤(s : ℝ)*((n : ℝ)*x)
      push_cast
      nlinarith [mul_le_mul_of_nonpos_left hx.2 hn']
    · change (s : ℝ)*((n : ℝ)*x)≤((n*I.lo : ℤ) : ℝ)
      push_cast
      nlinarith [mul_le_mul_of_nonpos_left hx.1 hn']
end ThomsonNine.FixedInterval
