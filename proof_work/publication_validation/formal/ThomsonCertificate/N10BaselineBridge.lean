import ThomsonCertificate.N10BaselineData
import ThomsonCertificate.DelsarteBridge

/-! Conditional n=10 baseline bridge.  The arithmetic coefficients are fixed by
`N10BaselineData`; the analytic minorant and harmonic/addition-theorem facts are
still explicit fields, so this module cannot silently claim the global bound. -/

namespace ThomsonTen

open ThomsonCertificate

structure N10BaselineObligations where
  D : DelsarteBridge 10 13
  coefficient_match : ∀ k, D.coeff k = n10BaselineCoeff k
  bound_match : D.lowerBound = (326807 / 10000 : ℝ)

theorem n10_baseline_bound_from_obligations
    (C : N10BaselineObligations) (x : C.D.Config) (hx : C.D.feasible x) :
    (326807 / 10000 : ℝ) ≤ C.D.energy x := by
  rw [← C.bound_match]
  exact DelsarteBridge.sound C.D x hx

end ThomsonTen
