import MainCoverage.TraceModel
import MainCoverage.RootTensor.DProof
import MainCoverage.DiagonalSound

noncomputable section
namespace ThomsonNine.PackedMain
open ThomsonNine.PackedTensor ThomsonNine.PackedRadix

theorem negative_actual_diagonal_root (t : ℝ) (ht : 0≤t ∧ t≤1) :
    uniValue 20 offset scale diagonalRootWord t≤-MainEnvelope.diagonal (point 0 0 t) := by
  simpa only [MainEnvelope.Archive.diagonal_eq_polynomial,RootTensor.D.archiveDiagonal] using
    RootTensor.D.negative_diagonal_root t ht

theorem actual_diagonal_lower (id : ℕ) (hid : id<4816) :
    DiagonalLower MainEnvelope.diagonal (diagonalLookup id) :=
  all_diagonal_lower MainEnvelope.diagonal negative_actual_diagonal_root id hid
end ThomsonNine.PackedMain
