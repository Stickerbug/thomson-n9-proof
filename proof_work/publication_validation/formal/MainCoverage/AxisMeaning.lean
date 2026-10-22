import MainCoverage.ActualDiagonal
import MainCoverage.AxisSound

noncomputable section
namespace ThomsonNine.PackedMain
open ThomsonNine.PackedRadix

def AxisActualLower (e : AxisEntry) : Prop := ∀ t, 0≤t ∧ t≤1 →
  axisCurve e t≤ThomsonNine.ActualCoulombGlobal.coulomb (point e.level e.index t)-
    MainEnvelope.diagonal (point e.level e.index t)

attribute [local irreducible] uniValue

theorem axis_witness_actual (e : AxisEntry) (w : AxisWitness) (id : ℕ) (hid : id<4816)
    (hl : (diagonalLookup id).level=e.level) (hi : (diagonalLookup id).index=e.index)
    (h : axisCertificateOK e (diagonalLookup id).word w=true) : AxisActualLower e := by
  intro t ht
  have hD : ∀ u, 0≤u ∧ u≤1 → uniValue 20 offset scale (diagonalLookup id).word u≤-MainEnvelope.diagonal (qPoint e u) := by
    intro u hu
    have hh := actual_diagonal_lower id hid u hu
    rw [hl,hi,← qPoint_eq e u] at hh
    exact hh
  have hh := axisCertificateOK_sound e (diagonalLookup id).word w h MainEnvelope.diagonal hD t ht
  simpa only [qPoint_eq] using hh
end ThomsonNine.PackedMain
