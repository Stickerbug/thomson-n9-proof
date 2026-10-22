import ThomsonNine.GroupedTranslation

noncomputable section
namespace ThomsonNine.FixedInterval
open ThomsonNine.Interval ThomsonNine.Interval.RatInterval
open ThomsonNine.Interval.SparsePolynomial
open ThomsonNine.Interval.SparsePolynomial.Grouped

/-- Integer endpoints scaled by the same positive integer. No validity premise is
trusted: a reversed pair simply cannot contain a real value. -/
structure Bounds where
  lo : ℤ
  hi : ℤ

def Mem (s : ℤ) (I : Bounds) (x : ℝ) : Prop :=
  (I.lo : ℝ) ≤ (s : ℝ) * x ∧ (s : ℝ) * x ≤ (I.hi : ℝ)

def zero : Bounds := ⟨0, 0⟩
def add (I J : Bounds) : Bounds := ⟨I.lo + J.lo, I.hi + J.hi⟩
def scale (n : ℕ) (I : Bounds) : Bounds := ⟨n * I.lo, n * I.hi⟩
def lowProduct (I J : Bounds) : ℤ :=
  min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi))
def highProduct (I J : Bounds) : ℤ :=
  max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))
def mul (s : ℤ) (I J : Bounds) : Bounds :=
  ⟨lowProduct I J / s, -((-highProduct I J) / s)⟩

def sum : List Bounds → Bounds
  | [] => zero
  | I :: l => add I (sum l)

def power (s : ℤ) (A : Bounds) : ℕ → Bounds
  | 0 => ⟨s, s⟩
  | n+1 => mul s (power s A n) A

theorem mem_zero (s : ℤ) : Mem s zero 0 := by simp [Mem, zero]
theorem mem_add {s : ℤ} {I J : Bounds} {x y : ℝ}
    (hx : Mem s I x) (hy : Mem s J y) : Mem s (add I J) (x+y) := by
  simp only [Mem, add, Int.cast_add] at *
  constructor <;> nlinarith [hx.1, hx.2, hy.1, hy.2]
theorem mem_scale {s : ℤ} {I : Bounds} {x : ℝ} (hx : Mem s I x) (n : ℕ) :
    Mem s (scale n I) ((n : ℝ)*x) := by
  simp only [Mem, scale, Int.cast_mul, Int.cast_natCast] at *
  constructor <;> nlinarith [hx.1, hx.2, (show (0 : ℝ) ≤ n by positivity)]

private theorem scalar_bounds {a b x t L U : ℝ}
    (hxlo : a ≤ x) (hxhi : x ≤ b)
    (hLa : L ≤ a*t) (hLb : L ≤ b*t) (haU : a*t ≤ U) (hbU : b*t ≤ U) :
    L ≤ x*t ∧ x*t ≤ U := by
  rcases le_total 0 t with ht | ht
  · exact ⟨le_trans hLa (mul_le_mul_of_nonneg_right hxlo ht),
      le_trans (mul_le_mul_of_nonneg_right hxhi ht) hbU⟩
  · exact ⟨le_trans hLb (mul_le_mul_of_nonpos_right hxhi ht),
      le_trans (mul_le_mul_of_nonpos_right hxlo ht) haU⟩

private theorem corners {a b c d x y L U : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (h0 : L ≤ a*c) (h1 : L ≤ a*d) (h2 : L ≤ b*c) (h3 : L ≤ b*d)
    (h4 : a*c ≤ U) (h5 : a*d ≤ U) (h6 : b*c ≤ U) (h7 : b*d ≤ U) :
    L ≤ x*y ∧ x*y ≤ U := by
  have ha := scalar_bounds (t := a) (L := L) (U := U) hy.1 hy.2
    (by simpa [mul_comm] using h0) (by simpa [mul_comm] using h1)
    (by simpa [mul_comm] using h4) (by simpa [mul_comm] using h5)
  have hb := scalar_bounds (t := b) (L := L) (U := U) hy.1 hy.2
    (by simpa [mul_comm] using h2) (by simpa [mul_comm] using h3)
    (by simpa [mul_comm] using h6) (by simpa [mul_comm] using h7)
  exact scalar_bounds (t := y) (L := L) (U := U) hx.1 hx.2
    (by simpa [mul_comm] using ha.1) (by simpa [mul_comm] using hb.1)
    (by simpa [mul_comm] using ha.2) (by simpa [mul_comm] using hb.2)

theorem mem_mul {s : ℤ} (hs : 0 < s) {I J : Bounds} {x y : ℝ}
    (hx : Mem s I x) (hy : Mem s J y) : Mem s (mul s I J) (x*y) := by
  have hcorner : (lowProduct I J : ℝ) ≤ ((s : ℝ)*x)*((s : ℝ)*y) ∧
      ((s : ℝ)*x)*((s : ℝ)*y) ≤ (highProduct I J : ℝ) := by
    apply corners hx hy <;> simp only [lowProduct, highProduct, Int.cast_min,
      Int.cast_max, Int.cast_mul] <;> simp only [min_le_iff, le_max_iff] <;> simp
  have hlo : (lowProduct I J / s) * s ≤ lowProduct I J := Int.ediv_mul_le _ (ne_of_gt hs)
  have hhi : ((-highProduct I J) / s) * s ≤ -highProduct I J :=
    Int.ediv_mul_le _ (ne_of_gt hs)
  have hlo' : ((lowProduct I J / s : ℤ) : ℝ) * (s : ℝ) ≤ (lowProduct I J : ℝ) := by exact_mod_cast hlo
  have hhi' : (highProduct I J : ℝ) ≤ (-((-highProduct I J) / s) : ℤ) * (s : ℝ) := by
    exact_mod_cast (show highProduct I J ≤ -((-highProduct I J) / s) * s by nlinarith [hhi])
  have hpos : (0 : ℝ) < s := by exact_mod_cast hs
  constructor
  · change ((lowProduct I J / s : ℤ) : ℝ) ≤ (s : ℝ) * (x*y)
    apply le_of_mul_le_mul_right (a := (s : ℝ)) _ hpos
    nlinarith [hcorner.1]
  · change (s : ℝ) * (x*y) ≤ (-((-highProduct I J) / s) : ℤ)
    apply le_of_mul_le_mul_right (a := (s : ℝ)) _ hpos
    nlinarith [hcorner.2]

theorem power_mem {s : ℤ} (hs : 0 < s) {A : Bounds} {a : ℝ}
    (ha : Mem s A a) (n : ℕ) : Mem s (power s A n) (a^n) := by
  induction n with
  | zero => simp [power, Mem]
  | succ n ih => simpa [power, pow_succ] using mem_mul hs ih ha

theorem sum_mem {s : ℤ} {α : Type*} (C : α → Bounds) (c : α → ℝ) (l : List α)
    (h : ∀ i ∈ l, Mem s (C i) (c i)) : Mem s (sum (l.map C)) (l.map c).sum := by
  induction l with
  | nil => exact mem_zero s
  | cons i l ih => exact mem_add (h i (by simp)) (ih (fun j hj => h j (by simp [hj])))

theorem mem_of_rat {s : ℤ} {I : Bounds} {K : RatInterval} {x : ℝ}
    (hx : K.mem x) (hs : 0 < s)
    (hlo : (I.lo : ℚ) ≤ (s : ℚ)*K.lo) (hhi : (s : ℚ)*K.hi ≤ (I.hi : ℚ)) : Mem s I x := by
  have hs' : (0 : ℝ) ≤ s := by exact_mod_cast le_of_lt hs
  have hl : (I.lo : ℝ) ≤ (s : ℝ)*(K.lo : ℝ) := by exact_mod_cast hlo
  have hh : (s : ℝ)*(K.hi : ℝ) ≤ (I.hi : ℝ) := by exact_mod_cast hhi
  exact ⟨hl.trans (mul_le_mul_of_nonneg_left hx.1 hs'),
    (mul_le_mul_of_nonneg_left hx.2 hs').trans hh⟩

theorem mem_to_rat {s : ℤ} {I : Bounds} {K : RatInterval} {x : ℝ}
    (hx : Mem s I x) (hs : 0 < s)
    (hlo : (s : ℚ)*K.lo ≤ (I.lo : ℚ)) (hhi : (I.hi : ℚ) ≤ (s : ℚ)*K.hi) : K.mem x := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hl : (s : ℝ)*(K.lo : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast hlo
  have hh : (I.hi : ℝ) ≤ (s : ℝ)*(K.hi : ℝ) := by exact_mod_cast hhi
  exact ⟨le_of_mul_le_mul_left (hl.trans hx.1) hs',
    le_of_mul_le_mul_left (hx.2.trans hh) hs'⟩

end ThomsonNine.FixedInterval

namespace ThomsonNine.FixedInterval
open ThomsonNine.Interval.SparsePolynomial

def factor (n k : ℕ) (P : ℕ → Bounds) : Bounds := scale (n.choose k) (P (n-k))
theorem factor_mem {s : ℤ} (n k : ℕ) (P : ℕ → Bounds) (a : ℝ)
    (hP : ∀ n, Mem s (P n) (a^n)) : Mem s (factor n k P) (shiftFactor n k a) :=
  mem_scale (hP (n-k)) (n.choose k)
end ThomsonNine.FixedInterval
