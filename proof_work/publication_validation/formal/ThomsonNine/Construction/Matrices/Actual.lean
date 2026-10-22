import ThomsonNine.Construction.Matrices.PSD
import ThomsonNine.Construction.Matrices.Bounds
import ThomsonNine.Construction.Contact.SystemCertificate
import ThomsonNine.Construction.Hermite.Energy

-- Isolated source: Matrices.Actual
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.CertificateMatrices
open ThomsonNine.FixedInterval ThomsonNine.FixedInterval.Schur ThomsonNine.ActualHermite.CoefficientData
theorem actual_Xinput_bounds : ∀ h : Fin 190, Contains (solutionInput h) (ActualContact.SystemCertificate.Xinput h) := by
  unfold Contains
  decide +kernel
theorem actual_X_mem (h : Fin 190) : Mem unitScale (solutionInput h) (ActualContact.SystemCertificate.X h) :=
  mem_contains (actual_Xinput_bounds h) (ActualContact.SystemCertificate.X_mem h)
theorem actual_reduced_psd (k : Fin 11) : (reduced ActualContact.SystemCertificate.X k).PosSemidef :=
  reduced_psd _ actual_X_mem k
theorem actual_A_psd (k : Fin 11) : (A ActualContact.SystemCertificate.X k).PosSemidef :=
  all_A_psd _ actual_X_mem k
theorem actual_A_mem (k : Fin 11) (a b : Fin (ambientDim k)) :
    Mem unitScale (Ainput k a b) (A ActualContact.SystemCertificate.X k a b) :=
  A_mem _ actual_X_mem k a b
theorem contact_energy_eq_family :
    ActualContact.E=familyEnergy RefinedRadius.radius := by
  rw [← ActualHermite.contact_energy_identity]
  simp [ActualContact.E,ActualContact.energyNodes,ActualContact.energyWeights,Fin.sum_univ_succ]
  ring
end ThomsonNine.CertificateMatrices
