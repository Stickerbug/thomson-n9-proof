import ThomsonNine.Construction.Moment.Data

-- Isolated source: Moment.QStep12
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.CandidateMoment
open ThomsonNine.ExactPolynomial
theorem q_step_12 : qStepValid 12 := by decide +kernel
end ThomsonNine.CandidateMoment
