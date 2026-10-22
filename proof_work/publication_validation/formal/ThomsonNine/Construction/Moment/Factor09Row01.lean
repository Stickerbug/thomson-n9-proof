import ThomsonNine.Construction.Moment.Data

-- Isolated source: Moment.Factor09Row01
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.CandidateMoment
open ThomsonNine.ExactPolynomial
theorem factor_row_09_01 : ∀ b : Fin 2, sub (moment 9 1 ⟨b.val,by omega⟩) (factor 9 1 ⟨b.val,by omega⟩)=[] := by decide +kernel
end ThomsonNine.CandidateMoment
