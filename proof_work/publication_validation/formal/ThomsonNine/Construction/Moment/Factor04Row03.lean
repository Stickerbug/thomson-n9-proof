import ThomsonNine.Construction.Moment.Data

-- Isolated source: Moment.Factor04Row03
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.CandidateMoment
open ThomsonNine.ExactPolynomial
theorem factor_row_04_03 : ∀ b : Fin 7, sub (moment 4 3 ⟨b.val,by omega⟩) (factor 4 3 ⟨b.val,by omega⟩)=[] := by decide +kernel
end ThomsonNine.CandidateMoment
