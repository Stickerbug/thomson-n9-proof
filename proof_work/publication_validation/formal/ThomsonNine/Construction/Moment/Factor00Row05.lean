import ThomsonNine.Construction.Moment.Data

-- Isolated source: Moment.Factor00Row05
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.CandidateMoment
open ThomsonNine.ExactPolynomial
theorem factor_row_00_05 : ∀ b : Fin 11, sub (moment 0 5 ⟨b.val,by omega⟩) (factor 0 5 ⟨b.val,by omega⟩)=[] := by decide +kernel
end ThomsonNine.CandidateMoment
