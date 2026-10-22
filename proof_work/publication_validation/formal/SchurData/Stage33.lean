import Algebra.SchurCertificate
import ThomsonNine.ActualHermiteScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.ContactSchur.Stage33
open ThomsonNine.FixedInterval ThomsonNine.FixedInterval.Schur
open ThomsonNine.ActualHermite.CoefficientData
def A : Fin 0 → Fin 0 → Bounds := Fin.elim0
def b : Fin 0 → Bounds := Fin.elim0
def solution : Fin 0 → Bounds := Fin.elim0
theorem certificate : Sound unitScale A b solution := empty_sound unitScale A b solution
end ThomsonNine.ContactSchur.Stage33
