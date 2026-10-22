import F.CoefficientCache
import Matrices.Actual
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ActualF.Certified
open ThomsonNine.ActualF.Data ThomsonNine.CertificateMatrices ThomsonNine.ActualHermite.CoefficientData ThomsonNine.FixedInterval
theorem bounds : ∀ j : Fin 756,
    (unitScale : ℚ)*(coefficientInterval j).lo≤(Cached.input j).lo ∧
    ((Cached.input j).hi : ℚ)≤(unitScale : ℚ)*(coefficientInterval j).hi := by decide +kernel
theorem coefficient_mem_archive (X : Fin 190 → ℝ) (hX : ∀ h, Mem unitScale (solutionInput h) (X h)) (j : Fin 756) :
    (coefficientInterval j).mem (coefficient X j) :=
  mem_to_rat (Cached.input_mem X hX j) unitScale_pos (bounds j).1 (bounds j).2
theorem actual_coefficient_mem (j : Fin 756) :
    (coefficientInterval j).mem (coefficient ActualContact.SystemCertificate.X j) :=
  coefficient_mem_archive _ actual_X_mem j
end ThomsonNine.ActualF.Certified
