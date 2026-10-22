import ThomsonNine.Construction.Moment.Data

-- Isolated source: Moment.Factor07Row03
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.CandidateMoment
open ThomsonNine.ExactPolynomial
theorem factor_row_07_03 : ∀ b : Fin 4, sub (moment 7 3 ⟨b.val,by omega⟩) (factor 7 3 ⟨b.val,by omega⟩)=[] := by decide +kernel
end ThomsonNine.CandidateMoment
