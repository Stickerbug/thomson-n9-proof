import ThomsonNine.Construction.Moment.Data

-- Isolated source: Moment.Factor03Row05
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.CandidateMoment
open ThomsonNine.ExactPolynomial
theorem factor_row_03_05 : ∀ b : Fin 8, sub (moment 3 5 ⟨b.val,by omega⟩) (factor 3 5 ⟨b.val,by omega⟩)=[] := by decide +kernel
end ThomsonNine.CandidateMoment
