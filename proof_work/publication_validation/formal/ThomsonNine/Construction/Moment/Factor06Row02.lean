import ThomsonNine.Construction.Moment.Data

-- Isolated source: Moment.Factor06Row02
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.CandidateMoment
open ThomsonNine.ExactPolynomial
theorem factor_row_06_02 : ∀ b : Fin 5, sub (moment 6 2 ⟨b.val,by omega⟩) (factor 6 2 ⟨b.val,by omega⟩)=[] := by decide +kernel
end ThomsonNine.CandidateMoment
