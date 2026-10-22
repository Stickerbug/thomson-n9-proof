import ThomsonNine.Construction.Moment.Data

-- Isolated source: Moment.Factor02Row04
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.CandidateMoment
open ThomsonNine.ExactPolynomial
theorem factor_row_02_04 : ∀ b : Fin 9, sub (moment 2 4 ⟨b.val,by omega⟩) (factor 2 4 ⟨b.val,by omega⟩)=[] := by decide +kernel
end ThomsonNine.CandidateMoment
