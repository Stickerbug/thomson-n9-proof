import Algebra.JetPolynomial
import Algebra.SchurCertificate

noncomputable section
namespace ThomsonNine.ContactJet
def Contains (outer inner : Input) : Prop :=
  FixedInterval.Schur.Contains outer.value inner.value ∧
    ∀ i, FixedInterval.Schur.Contains (outer.gradient i) (inner.gradient i)
theorem mem_contains {s : ℤ} {I J : Input} {a : Jet} (h : Contains I J) (ha : Mem s J a) :
    Mem s I a :=
  ⟨FixedInterval.Schur.mem_contains h.1 ha.1,fun i => FixedInterval.Schur.mem_contains (h.2 i) (ha.2 i)⟩
end ThomsonNine.ContactJet
