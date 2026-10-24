import ThomsonCertificate.GenericMinimum

/-! Optional equality-classification layer for a global minimum contract. -/

namespace ThomsonCertificate

structure EqualityClassification {n : ℕ} (C : GlobalMinimumContract n) where
  equivalent : C.Config → Prop
  characterize : ∀ x, C.feasible x →
    (C.energy x = C.candidateEnergy ↔ equivalent x)

namespace EqualityClassification

theorem iff {n : ℕ} {C : GlobalMinimumContract n}
    (U : EqualityClassification C) (x : C.Config) (hx : C.feasible x) :
    C.energy x = C.candidateEnergy ↔ U.equivalent x :=
  U.characterize x hx

end EqualityClassification

end ThomsonCertificate
