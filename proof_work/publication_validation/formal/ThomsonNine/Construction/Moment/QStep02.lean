import ThomsonNine.Construction.Moment.Data

-- Isolated source: Moment.QStep02
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.CandidateMoment
open ThomsonNine.ExactPolynomial
theorem q_step_02 : qStepValid 2 := by decide +kernel
end ThomsonNine.CandidateMoment
