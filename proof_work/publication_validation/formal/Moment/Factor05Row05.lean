import Moment.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.CandidateMoment
open ThomsonNine.ExactPolynomial
theorem factor_row_05_05 : ∀ b : Fin 6, sub (moment 5 5 ⟨b.val,by omega⟩) (factor 5 5 ⟨b.val,by omega⟩)=[] := by decide +kernel
end ThomsonNine.CandidateMoment
