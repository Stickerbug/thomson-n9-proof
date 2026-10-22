import ThomsonNine.IntervalSqrt

noncomputable section
namespace ThomsonNine.Interval.RatInterval

theorem mem_inv_of_bounds {I K : RatInterval} {x : ℝ} (hx : I.mem x)
    (hSign : 0<I.lo ∨ I.hi<0)
    (hlo : K.lo ≤ 1/I.hi) (hhi : 1/I.lo ≤ K.hi) : K.mem x⁻¹ := by
  rcases hSign with hp | hn
  · simpa only [one_div] using mem_subset (mem_reciprocalPos hp hx) hlo hhi
  · have hp : 0<(neg I).lo := by simpa only [neg] using neg_pos.mpr hn
    have h := mem_neg (mem_reciprocalPos hp (mem_neg hx))
    have h' : (neg (reciprocalPos (neg I) hp)).mem x⁻¹ := by
      simpa using h
    apply mem_subset h'
    · simpa [neg,reciprocalPos] using hlo
    · simpa [neg,reciprocalPos] using hhi
end ThomsonNine.Interval.RatInterval
