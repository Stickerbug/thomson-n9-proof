/-
Certificate semantics for a single Bernstein box.

A `LocalCert` bundles the coefficient box of a ternary Bernstein tensor together
with the three parameter intervals and the machine-checkable side condition that
the interval evaluation of the whole tensor has nonnegative lower endpoint.
`LocalCert.sound` turns that arithmetic side condition into a genuine
nonnegativity statement for the polynomial on the whole box.
-/
import ThomsonNine.IntervalTensorEval

namespace ThomsonNine
namespace Interval
namespace RatInterval

open ThomsonNine.Semantics (tensor)

/-- A single-box Bernstein certificate. -/
structure LocalCert where
  n : ℕ
  C : Fin (n+1) → Fin (n+1) → Fin (n+1) → RatInterval
  Iu : RatInterval
  Iv : RatInterval
  It : RatInterval
  hu0 : 0 ≤ Iu.lo
  hu1 : Iu.hi ≤ 1
  hv0 : 0 ≤ Iv.lo
  hv1 : Iv.hi ≤ 1
  ht0 : 0 ≤ It.lo
  ht1 : It.hi ≤ 1
  coeff_nonneg : 0 ≤ (evalTensor n C Iu Iv It hu0 hu1 hv0 hv1 ht0 ht1).lo

/-- Certificate soundness: on the whole box the represented tensor is nonnegative. -/
theorem LocalCert.sound (cert : LocalCert)
    (c : Fin (cert.n+1) → Fin (cert.n+1) → Fin (cert.n+1) → ℝ)
    (hC : ∀ i j k, (cert.C i j k).mem (c i j k))
    {u v t : ℝ} (hu : cert.Iu.mem u) (hv : cert.Iv.mem v) (ht : cert.It.mem t) :
    0 ≤ tensor cert.n c u v t := by
  have hmem := evalTensor_sound cert.n cert.C c hC cert.Iu cert.Iv cert.It
    cert.hu0 cert.hu1 cert.hv0 cert.hv1 cert.ht0 cert.ht1 hu hv ht
  have h0 : (0 : ℝ) ≤ ((evalTensor cert.n cert.C cert.Iu cert.Iv cert.It
      cert.hu0 cert.hu1 cert.hv0 cert.hv1 cert.ht0 cert.ht1).lo : ℝ) := by
    exact_mod_cast cert.coeff_nonneg
  exact le_trans h0 hmem.1

end RatInterval
end Interval
end ThomsonNine
