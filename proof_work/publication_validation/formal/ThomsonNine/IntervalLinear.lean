import ThomsonNine.IntervalLocalOps

/-! Exact signed linear interval maps for Hessian preconditioning.
No polynomial Hessian evaluation is asserted by these arithmetic lemmas. -/

namespace ThomsonNine.Interval.RatInterval

/-- Exact interval image under multiplication by an arbitrary rational. -/
def signedScale (q : ℚ) (I : RatInterval) : RatInterval :=
  if h : 0 ≤ q then scale q h I else neg (scale (-q) (by linarith) I)

theorem mem_signedScale (q : ℚ) {I : RatInterval} {x : ℝ} (hx : I.mem x) :
    (signedScale q I).mem ((q : ℝ) * x) := by
  unfold signedScale
  split_ifs with h
  · exact mem_scale h hx
  · convert mem_neg (mem_scale (show (0 : ℚ) ≤ -q by linarith) hx) using 1 <;>
      push_cast <;> ring

/-- A six-entry real linear map with exact rational coefficients. -/
def linear6 (a b c d e f : ℚ) (A B C D E F : ℝ) : ℝ :=
  (a : ℝ) * A + (b : ℝ) * B + (c : ℝ) * C +
    (d : ℝ) * D + (e : ℝ) * E + (f : ℝ) * F

/-- Interval image of the same linear map. -/
def linearInterval6 (a b c d e f : ℚ) (A B C D E F : RatInterval) : RatInterval :=
  add (add (add (add (add (signedScale a A) (signedScale b B))
    (signedScale c C)) (signedScale d D)) (signedScale e E)) (signedScale f F)

theorem mem_linear6 (a b c d e f : ℚ) {IA IB IC ID IE IF : RatInterval}
    {A B C D E F : ℝ} (hA : IA.mem A) (hB : IB.mem B) (hC : IC.mem C)
    (hD : ID.mem D) (hE : IE.mem E) (hF : IF.mem F) :
    (linearInterval6 a b c d e f IA IB IC ID IE IF).mem
      (linear6 a b c d e f A B C D E F) :=
  mem_add (mem_add (mem_add (mem_add (mem_add
    (mem_signedScale a hA) (mem_signedScale b hB)) (mem_signedScale c hC))
    (mem_signedScale d hD)) (mem_signedScale e hE)) (mem_signedScale f hF)

end ThomsonNine.Interval.RatInterval
