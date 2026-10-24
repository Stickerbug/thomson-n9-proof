import Mathlib

/-!
# Generic global-minimum contract

This is the statement-level interface above a certificate.  It records a
candidate, feasibility, its energy, and a global lower-bound proof.  Equality
classification is intentionally a separate optional theorem.
-/

namespace ThomsonCertificate

structure GlobalMinimumContract (n : ℕ) where
  Config : Type
  feasible : Config → Prop
  energy : Config → ℝ
  candidate : Config
  candidateEnergy : ℝ
  candidate_feasible : feasible candidate
  candidate_energy : energy candidate = candidateEnergy
  lower_bound : ∀ x, feasible x → candidateEnergy ≤ energy x

namespace GlobalMinimumContract

theorem bound {n : ℕ} (C : GlobalMinimumContract n) :
    ∀ x, C.feasible x → C.candidateEnergy ≤ C.energy x :=
  C.lower_bound

theorem candidate_attains {n : ℕ} (C : GlobalMinimumContract n) :
    C.energy C.candidate = C.candidateEnergy :=
  C.candidate_energy

end GlobalMinimumContract

end ThomsonCertificate
