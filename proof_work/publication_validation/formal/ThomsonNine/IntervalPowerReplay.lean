import ThomsonNine.IntervalSparsePolynomial

/-! Soundness of the generator's square/previous-power cache.
The endpoint witnesses are rational comparisons; this file asserts no archived
cache bounds or polynomial/residual identity. -/

namespace ThomsonNine.Interval.SparsePolynomial
open RatInterval

/-- A power cache can round outward after squaring even powers and multiplying
odd powers. Its rational endpoint checks imply real membership for every n. -/
theorem mem_powerCache (I : RatInterval) (P : ℕ → RatInterval)
    (hzero : P 0 = const 1)
    (hsquare : ∀ k, 0 < k →
      (P (2 * k)).lo ≤ (square (P k)).lo ∧
      (square (P k)).hi ≤ (P (2 * k)).hi)
    (hmul : ∀ k,
      (P (2 * k + 1)).lo ≤ (mul (P (2 * k)) I).lo ∧
      (mul (P (2 * k)) I).hi ≤ (P (2 * k + 1)).hi)
    {x : ℝ} (hx : I.mem x) (n : ℕ) : (P n).mem (x ^ n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.even_or_odd n with heven | hodd
    · obtain ⟨k, hk⟩ := heven
      have hn : n = 2 * k := by omega
      subst n
      by_cases hk0 : k = 0
      · subst k
        simpa [hzero] using mem_const (1 : ℚ)
      · have hkp : 0 < k := Nat.pos_of_ne_zero hk0
        have h := mem_subset (mem_square (ih k (by omega))) (hsquare k hkp).1
          (hsquare k hkp).2
        have hp : (x ^ k) ^ 2 = x ^ (k + k) := by
          rw [← pow_mul]
          congr 1
          omega
        simpa only [two_mul, hp] using h
    · obtain ⟨k, hk⟩ := hodd
      have hn : n = 2 * k + 1 := by omega
      subst n
      have h := mem_subset (mem_mul (ih (2 * k) (by omega)) hx)
        (hmul k).1 (hmul k).2
      simpa only [pow_succ] using h

end ThomsonNine.Interval.SparsePolynomial
