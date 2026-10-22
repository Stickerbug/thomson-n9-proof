import ThomsonNine.Construction.Algebra.JetPolynomial

-- Isolated source: Algebra.JetHornerProjection
noncomputable section
namespace ThomsonNine.ContactJet
open ThomsonNine.ListPolynomial

theorem horner_value (a : Jet) (l : List ℝ) :
    (horner a l).value=(polynomial l).eval a.value := by
  induction l with
  | nil => simp [horner,constant,polynomial]
  | cons b l ih =>
    change b+a.value*(horner a l).value = _
    rw [ih]
    simp [polynomial]

theorem horner_gradient (a : Jet) (l : List ℝ) (i : Fin 3) :
    (horner a l).gradient i=(polynomial l).derivative.eval a.value*a.gradient i := by
  induction l with
  | nil => simp [horner,constant,polynomial]
  | cons b l ih =>
    change 0+(a.gradient i*(horner a l).value+a.value*(horner a l).gradient i) = _
    rw [ih,horner_value]
    simp [polynomial]
    ring
end ThomsonNine.ContactJet
