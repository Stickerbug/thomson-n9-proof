import ThomsonNine.Construction.Moment.Data

-- Isolated source: Moment.Factor02Row00
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.CandidateMoment
open ThomsonNine.ExactPolynomial
theorem factor_row_02_00 : ∀ b : Fin 9, sub (moment 2 0 ⟨b.val,by omega⟩) (factor 2 0 ⟨b.val,by omega⟩)=[] := by decide +kernel
end ThomsonNine.CandidateMoment
