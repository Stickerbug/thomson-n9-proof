import Moment.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.CandidateMoment
open ThomsonNine.ExactPolynomial
theorem factor_row_04_04 : ∀ b : Fin 7, sub (moment 4 4 ⟨b.val,by omega⟩) (factor 4 4 ⟨b.val,by omega⟩)=[] := by decide +kernel
end ThomsonNine.CandidateMoment
