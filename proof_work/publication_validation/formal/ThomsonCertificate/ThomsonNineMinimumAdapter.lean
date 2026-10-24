import ThomsonCertificate.GenericMinimum
import MainCoverage.Final

/-! A statement-level n=9 instance of `GlobalMinimumContract`. -/

namespace ThomsonNine

open ThomsonCertificate

def n9WitnessPredicate (r : ℝ) : Prop :=
  0 < r ∧ r < 1 ∧ HasDerivAt familyEnergy 0 r ∧
    (∀ s : ℝ, 0 < s → s < 1 → HasDerivAt familyEnergy 0 s → s = r) ∧
    candidate r ∈ SphereConfig 9 ∧ energy (candidate r) = familyEnergy r ∧
    ∀ x ∈ SphereConfig 9, familyEnergy r ≤ energy x

theorem n9_witness_exists : ∃ r : ℝ, n9WitnessPredicate r :=
  ThomsonNine.thomsonNineClaim_proved

noncomputable def n9Witness : ℝ := Classical.choose n9_witness_exists

theorem n9Witness_spec : n9WitnessPredicate n9Witness :=
  Classical.choose_spec n9_witness_exists

noncomputable def n9GlobalMinimum : GlobalMinimumContract 9 := by
  exact
    { Config := Fin 9 → R3
      feasible := fun x => x ∈ SphereConfig 9
      energy := energy
      candidate := candidate n9Witness
      candidateEnergy := familyEnergy n9Witness
      candidate_feasible := n9Witness_spec.2.2.2.2.1
      candidate_energy := n9Witness_spec.2.2.2.2.2.1
      lower_bound := by
        intro x hx
        exact n9Witness_spec.2.2.2.2.2.2 x hx }

theorem n9_global_minimum_lower_bound (x : n9GlobalMinimum.Config)
    (hx : n9GlobalMinimum.feasible x) :
    n9GlobalMinimum.candidateEnergy ≤ n9GlobalMinimum.energy x :=
  n9GlobalMinimum.lower_bound x hx

theorem n9_global_minimum_candidate_attains :
    n9GlobalMinimum.energy n9GlobalMinimum.candidate =
      n9GlobalMinimum.candidateEnergy :=
  n9GlobalMinimum.candidate_energy

end ThomsonNine
