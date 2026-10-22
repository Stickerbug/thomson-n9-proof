import ThomsonNine.FixedInterval

noncomputable section
namespace ThomsonNine.FixedInterval

def neg (I : Bounds) : Bounds := ⟨-I.hi,-I.lo⟩
def constant (s n : ℤ) : Bounds := ⟨s*n,s*n⟩

theorem mem_neg {s : ℤ} {I : Bounds} {x : ℝ} (hx : Mem s I x) : Mem s (neg I) (-x) := by
  simp only [Mem,neg,Int.cast_neg] at *
  constructor <;> nlinarith [hx.1,hx.2]
theorem mem_constant (s n : ℤ) : Mem s (constant s n) (n : ℝ) := by
  simp [Mem,constant,Int.cast_mul]
end ThomsonNine.FixedInterval
