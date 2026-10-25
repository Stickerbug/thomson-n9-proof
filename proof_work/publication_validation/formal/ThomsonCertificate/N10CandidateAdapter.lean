import ThomsonCertificate.GenericMinimum
import ThomsonCertificate.N10CandidateInterval
import ThomsonCertificate.N10D4dGeometry

/-!
# Conditional n=10 D4d candidate adapter

This module packages the exact D4d candidate layers into the generic global
minimum contract.  The `lower_bound` field is deliberately an explicit input:
this file does not claim to prove the ten-point global lower bound.
-/

namespace ThomsonTen

open ThomsonNine
open ThomsonCertificate

noncomputable def d4dHeightOfT (t : ℝ) : ℝ :=
  (1 - t ^ 2) / (1 + t ^ 2)

structure D4dCandidateCertificate where
  t : ℝ
  t_mem : tInterval.mem t
  stationarity : d4dStationarity t = 0
  lower_bound : ∀ x : Fin 10 → R3, x ∈ SphereConfig 10 →
    d4dEnergyFormula (d4dHeightOfT t) ≤ energy x

lemma d4dHeightOfT_bounds (C : D4dCandidateCertificate) :
    0 < d4dHeightOfT C.t ∧ d4dHeightOfT C.t < 1 := by
  have hm := h_map_mem_interval C.t_mem
  have hlo := h_interval_inside_unit.1
  have hhi := h_interval_inside_unit.2
  exact ⟨lt_of_lt_of_le hlo hm.1, lt_of_le_of_lt hm.2 hhi⟩

lemma d4dCandidate_feasible (C : D4dCandidateCertificate) :
    d4dConfig (d4dHeightOfT C.t) ∈ SphereConfig 10 := by
  have hh := d4dHeightOfT_bounds C
  exact d4d_mem_sphereConfig hh.1 hh.2

noncomputable def d4dGlobalMinimumContract
    (C : D4dCandidateCertificate) : GlobalMinimumContract 10 :=
  { Config := Fin 10 → R3
    feasible := fun x => x ∈ SphereConfig 10
    energy := energy
    candidate := d4dConfig (d4dHeightOfT C.t)
    candidateEnergy := d4dEnergyFormula (d4dHeightOfT C.t)
    candidate_feasible := d4dCandidate_feasible C
    candidate_energy := by
      have hh := d4dHeightOfT_bounds C
      exact d4d_energy_eq_formula hh.1 hh.2
    lower_bound := C.lower_bound }

theorem d4d_global_lower_bound_from_certificate
    (C : D4dCandidateCertificate) (x : Fin 10 → R3)
    (hx : x ∈ SphereConfig 10) :
    (d4dGlobalMinimumContract C).candidateEnergy ≤
      (d4dGlobalMinimumContract C).energy x :=
  (d4dGlobalMinimumContract C).lower_bound x hx

theorem d4d_candidate_attains_from_certificate
    (C : D4dCandidateCertificate) :
    (d4dGlobalMinimumContract C).energy
        (d4dGlobalMinimumContract C).candidate =
      (d4dGlobalMinimumContract C).candidateEnergy :=
  (d4dGlobalMinimumContract C).candidate_energy

end ThomsonTen
